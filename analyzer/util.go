// Copyright 2023 Google LLC
//
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file or at
// https://developers.google.com/open-source/licenses/bsd

package analyzer

import (
	"go/ast"
	"go/token"
	"go/types"
	"os"
	"path"
	"strings"

	cpb "github.com/google/capslock/proto"
	"golang.org/x/tools/go/callgraph"
	"golang.org/x/tools/go/callgraph/vta"
	"golang.org/x/tools/go/packages"
	"golang.org/x/tools/go/ssa"
	"golang.org/x/tools/go/ssa/ssautil"
)

type bfsState struct {
	// edge is the callgraph edge leading to the next node in a path to an
	// interesting function.
	edge *cpb.Graph_Call
}

// bfsStateMap represents the state of a BFS search, and can be used to trace
// paths from the initial nodes of the search to any other node reached.
type bfsStateMap map[int64]bfsState

type nodeset map[int64]struct{}
type nodesetPerCapability map[cpb.Capability]nodeset

func (nc nodesetPerCapability) add(cap cpb.Capability, node int64) {
	m := nc[cap]
	if m == nil {
		m = make(nodeset)
		nc[cap] = m
	}
	m[node] = struct{}{}
}

func compareEdges(g *cpb.Graph, x, y *cpb.Graph_Call) int {
	if a, b := x.GetCaller(), y.GetCaller(); a != b {
		if c := compareFunctions(g, a, b); c != 0 {
			return c
		}
	}
	if a, b := x.GetCallee(), y.GetCallee(); a != b {
		if c := compareFunctions(g, a, b); c != 0 {
			return c
		}
	}
	return compareSites(x.CallSite, y.CallSite)
}

// compareBool performs a three-way comparison between two bool values.  It returns:
//
//	0  if a==b
//	-1 if a && !b
//	+1 if !a && b
func compareBool(a, b bool) int {
	if a == b {
		return 0
	}
	if a {
		return -1
	}
	return +1
}

func compareFunctions(g *cpb.Graph, x, y int64) int {
	a := g.Functions[x]
	b := g.Functions[y]
	return compareFunctionObjects(g, a, b)
}

func compareFunctionObjects(g *cpb.Graph, a, b *cpb.Graph_Function) int {
	ap := a.Package
	bp := b.Package
	if c := compareBool(ap != nil, bp != nil); c != 0 {
		return c
	}
	if ap != nil && bp != nil {
		if c := strings.Compare(g.Packages[*ap].GetPath(), g.Packages[*bp].GetPath()); c != 0 {
			return c
		}
	}
	hasReceiver := func(f *cpb.Graph_Function) bool {
		return f.Type != nil
	}
	if c := compareBool(!hasReceiver(a), !hasReceiver(b)); c != 0 {
		return c
	}
	return strings.Compare(a.GetName(), b.GetName())
}

func compareSites(x, y *cpb.Graph_Site) int {
	if x == y {
		return 0
	}
	if c := compareBool(x != nil, y != nil); c != 0 {
		return c
	}
	if c := compareBool(x.GetFilename() != "", y.GetFilename() != ""); c != 0 {
		return c
	}
	if c := compareBool(x.GetLine() != 0, y.GetLine() != 0); c != 0 {
		return c
	}
	if c := strings.Compare(x.GetFilename(), y.GetFilename()); c != 0 {
		return c
	}
	compareInt64 := func(a, b int64) int {
		if a == b {
			return 0
		}
		if a < b {
			return -1
		}
		return +1
	}
	if c := compareInt64(x.GetLine(), y.GetLine()); c != 0 {
		return c
	}
	return compareInt64(x.GetColumn(), y.GetColumn())
}

// callsitePosition returns a token.Position for the edge's callsite.
// If edge is nil, or the source is unavailable, the returned token.Position
// will have token.IsValid() == false.
func callsitePosition(edge *callgraph.Edge) token.Position {
	if edge == nil {
		return token.Position{}
	} else if f := edge.Caller.Func; f == nil {
		return token.Position{}
	} else if prog := f.Prog; prog == nil {
		return token.Position{}
	} else if fset := prog.Fset; fset == nil {
		return token.Position{}
	} else {
		return fset.Position(edge.Pos())
	}
}

func buildGraph(pkgs []*packages.Package, populateSyntax bool) (*callgraph.Graph, *ssa.Program, map[*ssa.Function]bool) {
	rewriteCallsToSort(pkgs)
	rewriteCallsToOnceDoEtc(pkgs)
	ssaBuilderMode := ssa.InstantiateGenerics
	if populateSyntax {
		// Debug mode makes ssa.Function.Syntax() point to the ast Node for the
		// function.  This will allow us to link nodes in the callgraph with
		// functions in the syntax tree which convert unsafe.Pointer objects or
		// use the reflect package in notable ways.
		ssaBuilderMode |= ssa.GlobalDebug
	}
	ssaProg, _ := ssautil.AllPackages(pkgs, ssaBuilderMode)
	ssaProg.Build()
	allFunctions := ssautil.AllFunctions(ssaProg)
	graph := vta.CallGraph(allFunctions, nil)
	return graph, ssaProg, allFunctions
}

// functionsToRewrite lists the functions and methods like (*sync.Once).Do that
// rewriteCallsToOnceDoEtc will rewrite to calls to their arguments.
var functionsToRewrite = []matcher{
	&methodMatcher{
		pkg:                         "sync",
		typeName:                    "Once",
		methodName:                  "Do",
		functionTypedParameterIndex: 0,
	},
	&packageFunctionMatcher{
		pkg:                         "sort",
		functionName:                "Slice",
		functionTypedParameterIndex: 1,
	},
	&packageFunctionMatcher{
		pkg:                         "sort",
		functionName:                "SliceStable",
		functionTypedParameterIndex: 1,
	},
}

type matcher interface {
	// match checks if a CallExpr is a call to a particular function or method
	// that this object is looking for.  If it matches, it returns a particular
	// argument in the call that has a function type.  Otherwise it returns nil.
	match(*types.Info, *ast.CallExpr) ast.Expr
}

// packageFunctionMatcher objects match a package-scope function.
type packageFunctionMatcher struct {
	pkg                         string
	functionName                string
	functionTypedParameterIndex int
}

// methodMatcher objects match a method of some type.
type methodMatcher struct {
	pkg                         string
	typeName                    string
	methodName                  string
	functionTypedParameterIndex int
}

func (m *packageFunctionMatcher) match(typeInfo *types.Info, call *ast.CallExpr) ast.Expr {
	callee, ok := call.Fun.(*ast.SelectorExpr)
	if !ok {
		// The function to be called is not a selection, so it can't be a call to
		// the relevant package.  (Unless the user has dot-imported the package,
		// but we don't need to worry much about false negatives in unusual cases
		// here.)
		return nil
	}
	pkgIdent, ok := callee.X.(*ast.Ident)
	if !ok {
		// The left-hand side of the selection is not a plain identifier.
		return nil
	}
	pkgName, ok := typeInfo.Uses[pkgIdent].(*types.PkgName)
	if !ok {
		// The identifier does not refer to a package.
		return nil
	}
	if pkgName.Imported().Path() != m.pkg {
		// Not the right package.
		return nil
	}
	if name := callee.Sel.Name; name != m.functionName {
		// This isn't the function we're looking for.
		return nil
	}
	if len(call.Args) <= m.functionTypedParameterIndex {
		// The function call doesn't have enough arguments.
		return nil
	}
	return call.Args[m.functionTypedParameterIndex]
}

// mayHaveSideEffects determines whether an expression might write to a
// variable or call a function.  It can have false positives.  It does not
// consider panicking to be a side effect, so e.g. index expressions do not
// have side effects unless one of its components do.
//
// This is used to determine whether we can delete the expression from the
// syntax tree in isCallToOnceDoEtc.
func mayHaveSideEffects(e ast.Expr) bool {
	switch e := e.(type) {
	case *ast.Ident, *ast.BasicLit:
		return false
	case nil:
		return false // we can reach a nil via *ast.SliceExpr
	case *ast.FuncLit:
		return false // a definition doesn't do anything on its own
	case *ast.CallExpr:
		return true
	case *ast.CompositeLit:
		for _, elt := range e.Elts {
			if mayHaveSideEffects(elt) {
				return true
			}
		}
		return false
	case *ast.ParenExpr:
		return mayHaveSideEffects(e.X)
	case *ast.SelectorExpr:
		return mayHaveSideEffects(e.X)
	case *ast.IndexExpr:
		return mayHaveSideEffects(e.X) || mayHaveSideEffects(e.Index)
	case *ast.IndexListExpr:
		for _, idx := range e.Indices {
			if mayHaveSideEffects(idx) {
				return true
			}
		}
		return mayHaveSideEffects(e.X)
	case *ast.SliceExpr:
		return mayHaveSideEffects(e.X) ||
			mayHaveSideEffects(e.Low) ||
			mayHaveSideEffects(e.High) ||
			mayHaveSideEffects(e.Max)
	case *ast.TypeAssertExpr:
		return mayHaveSideEffects(e.X)
	case *ast.StarExpr:
		return mayHaveSideEffects(e.X)
	case *ast.UnaryExpr:
		return mayHaveSideEffects(e.X)
	case *ast.BinaryExpr:
		return mayHaveSideEffects(e.X) || mayHaveSideEffects(e.Y)
	case *ast.KeyValueExpr:
		return mayHaveSideEffects(e.Key) || mayHaveSideEffects(e.Value)
	}
	return true
}

func (m *methodMatcher) match(typeInfo *types.Info, call *ast.CallExpr) ast.Expr {
	sel, ok := call.Fun.(*ast.SelectorExpr)
	if !ok {
		return nil
	}
	if mayHaveSideEffects(sel.X) {
		// The expression may be something like foo().Do(bar), which we can't
		// rewrite to a call to bar because then the analysis would not see the
		// call to foo.
		return nil
	}
	calleeType := typeInfo.TypeOf(sel.X)
	if calleeType == nil {
		return nil
	}
	if ptr, ok := types.Unalias(calleeType).(*types.Pointer); ok {
		calleeType = ptr.Elem()
	}
	named, ok := types.Unalias(calleeType).(*types.Named)
	if !ok {
		return nil
	}
	if named.Obj().Pkg() == nil {
		// Not in a package.
		return nil
	}
	if pkg := named.Obj().Pkg().Path(); pkg != m.pkg {
		// Not the right package.
		return nil
	}
	if named.Obj().Name() != m.typeName {
		// Not the right type.
		return nil
	}
	if name := sel.Sel.Name; name != m.methodName {
		// Not the right method.
		return nil
	}
	if len(call.Args) <= m.functionTypedParameterIndex {
		// The method call doesn't have enough arguments.
		return nil
	}
	return call.Args[m.functionTypedParameterIndex]
}

// visitor is passed to ast.Visit, to find AST nodes where
// unsafe.Pointer values are converted to pointers.
// It satisfies the ast.Visitor interface.
type visitor struct {
	// The sets we are populating.
	unsafeFunctionNodes map[ast.Node]struct{}
	// Set to true if an unsafe.Pointer conversion is found that is not inside
	// a function, method, or function literal definition.
	seenUnsafePointerUseInInitialization *bool
	// The Package for the ast Node being visited.  This is used to get type
	// information.
	pkg *packages.Package
	// The node for the current function being visited.  When function definitions
	// are nested, this is the innermost function.
	currentFunction ast.Node // *ast.FuncDecl or *ast.FuncLit
}

// containsReflectValue returns true if t is reflect.Value, or is a struct
// or array containing reflect.Value.
func containsReflectValue(t types.Type) bool {
	seen := map[types.Type]struct{}{}
	var rec func(t types.Type) bool
	rec = func(t types.Type) bool {
		if t == nil {
			return false
		}
		if t.String() == "reflect.Value" {
			return true
		}
		// avoid an infinite loop if the type is recursive somehow.
		if _, ok := seen[t]; ok {
			return false
		}
		seen[t] = struct{}{}
		// If the unaliased type is different, use that.
		if u := types.Unalias(t); u != t {
			return rec(u)
		}
		// If the underlying type is different, use that.
		if u := t.Underlying(); !types.Identical(t, u) {
			return rec(u)
		}
		// Check fields of structs.
		if s, ok := t.(*types.Struct); ok {
			for i := 0; i < s.NumFields(); i++ {
				if rec(s.Field(i).Type()) {
					return true
				}
			}
		}
		// Check elements of arrays.
		if a, ok := t.(*types.Array); ok {
			return rec(a.Elem())
		}
		return false
	}
	return rec(t)
}

func (v *visitor) Visit(node ast.Node) ast.Visitor {
	if node == nil {
		return v // the return value is ignored if node == nil.
	}
	switch node := node.(type) {
	case *ast.FuncDecl, *ast.FuncLit:
		// The subtree at this node is a function definition or function literal.
		// The visitor returned here is used to visit this node's children, so we
		// return a visitor with the current function set to this node.
		v2 := *v
		v2.currentFunction = node
		return &v2
	case *ast.CallExpr:
		// A type conversion is represented as a CallExpr node with a Fun that is a
		// type, and Args containing the expression to be converted.
		//
		// If this node has a single argument which is an unsafe.Pointer (or
		// is equivalent to an unsafe.Pointer) and the callee is a type which is not
		// uintptr, we add the current function to v.unsafeFunctionNodes.
		funType := v.pkg.TypesInfo.Types[node.Fun]
		if !funType.IsType() {
			// The callee is not a type; it's probably a function or method.
			break
		}
		if b, ok := funType.Type.Underlying().(*types.Basic); ok && b.Kind() == types.Uintptr {
			// The conversion is to a uintptr, not a pointer.  On its own, this is
			// safe.
			break
		}
		var args []ast.Expr = node.Args
		if len(args) != 1 {
			// There wasn't the right number of arguments.
			break
		}
		argType := v.pkg.TypesInfo.Types[args[0]].Type
		if argType == nil {
			// The argument has no type information.
			break
		}
		if b, ok := argType.Underlying().(*types.Basic); !ok || b.Kind() != types.UnsafePointer {
			// The argument's type is not equivalent to unsafe.Pointer.
			break
		}
		if v.currentFunction == nil {
			*v.seenUnsafePointerUseInInitialization = true
		} else {
			v.unsafeFunctionNodes[v.currentFunction] = struct{}{}
		}
	}
	return v
}

// forEachPackageIncludingDependencies calls fn exactly once for each package
// that is in pkgs or in the transitive dependencies of pkgs.
func forEachPackageIncludingDependencies(pkgs []*packages.Package, fn func(*packages.Package)) {
	visitedPackages := make(map[*packages.Package]struct{})
	var visit func(p *packages.Package)
	visit = func(p *packages.Package) {
		if _, ok := visitedPackages[p]; ok {
			return
		}
		visitedPackages[p] = struct{}{}
		for _, p2 := range p.Imports {
			visit(p2)
		}
		fn(p)
	}
	for _, p := range pkgs {
		visit(p)
	}
}

func programName() string {
	if a := os.Args; len(a) >= 1 {
		return path.Base(a[0])
	}
	return "capslock"
}

// addFunction adds an entry to *fns for the given graph function and call.
// The edge can be nil.
func addFunction(fns *[]*cpb.Function, graph *cpb.Graph, v int64, incomingEdge *cpb.Graph_Call) {
	fn := &cpb.Function{Name: graph.Functions[v].Name}
	if p := graph.Functions[v].Package; p != nil {
		fn.Package = graph.Packages[*p].Path
	}
	if incomingEdge != nil {
		if s := incomingEdge.CallSite; s != nil {
			fn.Site = &cpb.Function_Site{
				Filename: s.Filename,
				Line:     s.Line,
				Column:   s.Column,
			}
		}
	}
	*fns = append(*fns, fn)
}

// nodeToPackage returns the package of the node's function, or nil if it has
// no associated package, e.g. because it is a wrapper function.
func nodeToPackage(node *callgraph.Node) *types.Package {
	fn := node.Func
	// receiverTypePackage returns the package of a method given the type of its
	// receiver.
	receiverTypePackage := func(typ types.Type) *types.Package {
		if typ == nil {
			return nil
		}
		if p, ok := types.Unalias(typ).(*types.Pointer); ok {
			typ = p.Elem()
		}
		if n, ok := types.Unalias(typ).(*types.Named); ok {
			if pkg := n.Obj().Pkg(); pkg != nil {
				return pkg
			}
		}
		return nil
	}
	// Ordinary functions and methods.
	if pkg := fn.Package(); pkg != nil {
		return pkg.Pkg
	}
	// Generic functions and methods.
	if o := fn.Origin(); o != nil {
		if pkg := o.Package(); pkg != nil {
			return pkg.Pkg
		}
	}
	// Method expressions.
	if strings.HasSuffix(fn.Name(), "$thunk") {
		if len(fn.Params) > 0 {
			return receiverTypePackage(fn.Params[0].Object().Type())
		}
	}
	// Method values.
	if strings.HasSuffix(fn.Name(), "$bound") {
		if len(fn.FreeVars) >= 1 {
			return receiverTypePackage(fn.FreeVars[0].Type())
		}
	}
	// Other wrappers.
	if sig := fn.Signature; sig != nil {
		if recv := sig.Recv(); recv != nil {
			if t := recv.Type(); t != nil {
				if p := receiverTypePackage(t); p != nil {
					return p
				}
			}
		}
	}
	return nil
}
