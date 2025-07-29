// Copyright 2023 Google LLC
//
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file or at
// https://developers.google.com/open-source/licenses/bsd

package analyzer

import (
	"go/ast"
	"go/types"
	"maps"
	"path"
	"slices"
	"sort"
	"strings"

	"github.com/google/capslock/interesting"
	cpb "github.com/google/capslock/proto"
	"golang.org/x/tools/go/callgraph"
	"golang.org/x/tools/go/packages"
	"golang.org/x/tools/go/ssa"
	"google.golang.org/protobuf/proto"
)

// Config holds configuration for the analyzer.
type Config struct {
	// Classifier is used to assign capabilities to functions.
	Classifier Classifier
	// DisableBuiltin disables some additional source-code analyses that find
	// more capabilities in functions.
	DisableBuiltin bool
	// Granularity determines whether capability sets are examined per-package
	// or per-function when doing comparisons.
	Granularity Granularity
	// CapabilitySet is the set of capabilities to use for graph output mode.
	// If CapabilitySet is nil, all capabilities are used.
	CapabilitySet *CapabilitySet
	// OmitPaths disables output of example call paths.
	OmitPaths bool
}

// Classifier is an interface for types that help map code features to
// capabilities.
type Classifier interface {
	// FunctionCategory returns a Category for the given function specified by
	// a package name and function name.  Examples of function names include
	// "math.Cos", "(time.Time).Clock", and "(*sync.Cond).Signal".
	//
	// If the return value is Unspecified, then we have not declared it to be
	// either safe or unsafe, so its descendants will have to be considered by the
	// static analysis.
	FunctionCategory(pkg string, name string) cpb.Capability

	// IncludeCall returns true if a call from one function to another should be
	// considered when searching for transitive capabilities.  Usually this should
	// return true, unless there is some reason to know that the particular call
	// cannot lead to additional capabilities for a function.
	IncludeCall(edge *callgraph.Edge) bool
}

// GetClassifier returns a classifier for mapping packages and functions to the
// appropriate capability.
// If excludedUnanalyzed is true, the UNANALYZED capability is never returned.
func GetClassifier(excludeUnanalyzed bool) *interesting.Classifier {
	classifier := interesting.DefaultClassifier()
	if excludeUnanalyzed {
		return interesting.ClassifierExcludingUnanalyzed(classifier)
	}
	return classifier
}

// GetCapabilityInfo analyzes the input Graph.  It finds functions in
// the root packages that have a path in the callgraph to a function with a
// capability.
//
// GetCapabilityInfo does not return every possible path (see the function
// CapabilityGraph for a way to get all paths).  Which entries are returned
// depends on the value of Config.Granularity:
//   - For "function" granularity (the default), one CapabilityInfo is returned
//     for each combination of capability and root package function.
//   - For "package" granularity, one CapabilityInfo is returned for each
//     combination of capability and root package.
//   - For "intermediate" granularity, one CapabilityInfo is returned for each
//     combination of capability and package that is in a path from a root
//     package function to a function with a capability.
func GetCapabilityInfo(graph *cpb.Graph, config *Config) *cpb.CapabilityInfoList {
	if config.Granularity == GranularityUnset {
		config.Granularity = GranularityFunction
	}
	if config.Granularity == GranularityIntermediate {
		return intermediatePackages(graph, config)
	}
	type output struct {
		*cpb.CapabilityInfo
		Function int64 // used for sorting
	}
	var caps []output
	forEachPath(graph,
		func(cap cpb.Capability, nodes bfsStateMap, v int64) {
			var (
				c = cpb.CapabilityInfo{
					Capability:     cap.Enum(),
					CapabilityType: cpb.CapabilityType_CAPABILITY_TYPE_DIRECT.Enum(),
				}
				v0           = v
				firstPackage *cpb.Graph_Package
				incomingEdge *cpb.Graph_Call
			)
			if p := graph.Functions[v].Package; p != nil {
				firstPackage = graph.Packages[*p]
				c.PackageDir = firstPackage.Path
				c.PackageName = firstPackage.Name
			}
			for {
				if !config.OmitPaths || (v == v0 && config.Granularity == GranularityFunction) {
					addFunction(&c.Path, graph, v, incomingEdge)
				}
				if pi := graph.Functions[v].Package; pi != nil {
					if p := graph.Packages[*pi]; p != firstPackage && !p.GetIsStandardLibrary() {
						*c.CapabilityType = cpb.CapabilityType_CAPABILITY_TYPE_TRANSITIVE
					}
				}
				incomingEdge = nodes[v].edge
				if incomingEdge == nil {
					break
				}
				v = incomingEdge.GetCallee()
			}
			if !config.OmitPaths {
				var b strings.Builder
				for i, p := range c.Path {
					if i != 0 {
						b.WriteByte(' ')
					}
					b.WriteString(p.GetName())
				}
				c.DepPath = proto.String(b.String())
			}
			caps = append(caps, output{&c, v0})
		})
	sort.Slice(caps, func(i, j int) bool {
		if x, y := caps[i].CapabilityInfo.GetCapability(), caps[j].CapabilityInfo.GetCapability(); x != y {
			return x < y
		}
		return compareFunctions(graph, caps[i].Function, caps[j].Function) < 0
	})
	if config.Granularity == GranularityPackage {
		// Keep only the first entry in the sorted list for each (capability, package) pair.
		type cp struct {
			cpb.Capability
			Package int64
		}
		seen := make(map[cp]struct{})
		// del returns true if the capability and package of o have been seen before.
		del := func(o output) bool {
			pkg := graph.Functions[o.Function].Package
			if pkg == nil {
				return true
			}
			cp := cp{o.CapabilityInfo.GetCapability(), *pkg}
			if _, ok := seen[cp]; ok {
				return true
			}
			seen[cp] = struct{}{}
			return false
		}
		caps = slices.DeleteFunc(caps, del)
	}
	cil := &cpb.CapabilityInfoList{
		CapabilityInfo: make([]*cpb.CapabilityInfo, len(caps)),
		ModuleInfo:     collectModuleInfo(graph),
		PackageInfo:    collectPackageInfo(graph),
	}
	for i := range caps {
		cil.CapabilityInfo[i] = caps[i].CapabilityInfo
	}
	return cil
}

type CapabilityCounter struct {
	capability       cpb.Capability
	count            int64
	direct_count     int64
	transitive_count int64
	example          []*cpb.Function
}

// GetCapabilityStats analyzes the packages in pkgs.  For each function in
// those packages which have a path in the callgraph to an "interesting"
// function (see the "interesting" package), we give aggregated statistics
// about the capability usage.
func GetCapabilityStats(graph *cpb.Graph, config *Config) *cpb.CapabilityStatList {
	var cs []*cpb.CapabilityStats
	cm := make(map[string]*CapabilityCounter)
	forEachPath(graph,
		func(cap cpb.Capability, nodes bfsStateMap, v int64) {
			if _, ok := cm[cap.String()]; !ok {
				cm[cap.String()] = &CapabilityCounter{count: 1, capability: cap}
			} else {
				cm[cap.String()].count += 1
			}
			var (
				v0           = v
				firstPackage *cpb.Graph_Package
				incomingEdge *cpb.Graph_Call
				isDirect     = true
				example      []*cpb.Function
			)
			if p := graph.Functions[v].Package; p != nil {
				firstPackage = graph.Packages[*p]
			}
			for {
				if !config.OmitPaths || v == v0 {
					addFunction(&example, graph, v, incomingEdge)
				}
				if pi := graph.Functions[v].Package; pi != nil {
					if p := graph.Packages[*pi]; p != firstPackage && !p.GetIsStandardLibrary() {
						isDirect = false
					}
				}
				incomingEdge = nodes[v].edge
				if incomingEdge == nil {
					break
				}
				v = incomingEdge.GetCallee()
			}
			if isDirect {
				if _, ok := cm[cap.String()]; !ok {
					cm[cap.String()] = &CapabilityCounter{count: 1, direct_count: 1}
				} else {
					cm[cap.String()].direct_count += 1
				}
			} else {
				if _, ok := cm[cap.String()]; !ok {
					cm[cap.String()] = &CapabilityCounter{count: 1, transitive_count: 1}
				} else {
					cm[cap.String()].transitive_count += 1
				}
			}
			if _, ok := cm[cap.String()]; !ok {
				cm[cap.String()] = &CapabilityCounter{example: example}
			} else {
				cm[cap.String()].example = example
			}
		})
	for _, counts := range cm {
		cs = append(cs, &cpb.CapabilityStats{
			Capability:      &counts.capability,
			Count:           &counts.count,
			DirectCount:     &counts.direct_count,
			TransitiveCount: &counts.transitive_count,
			ExampleCallpath: counts.example,
		})
	}
	sort.Slice(cs, func(i, j int) bool {
		return cs[i].GetCapability() < cs[j].GetCapability()
	})
	return &cpb.CapabilityStatList{
		CapabilityStats: cs,
		ModuleInfo:      collectModuleInfo(graph),
	}
}

// GetCapabilityCounts analyzes the packages in pkgs.  For each function in
// those packages which have a path in the callgraph to an "interesting"
// function (see the "interesting" package), we give an aggregate count of the
// capability usage.
func GetCapabilityCounts(graph *cpb.Graph) *cpb.CapabilityCountList {
	cm := make(map[string]int64)
	forEachPath(graph,
		func(cap cpb.Capability, nodes bfsStateMap, v int64) {
			if _, ok := cm[cap.String()]; !ok {
				cm[cap.String()] = 1
			} else {
				cm[cap.String()] += 1
			}
		})
	return &cpb.CapabilityCountList{
		CapabilityCounts: cm,
		ModuleInfo:       collectModuleInfo(graph),
	}
}

// searchBackwardsFromCapabilities returns the set of all function nodes that
// have a path in the call graph to a function in nodesByCapability.
func searchBackwardsFromCapabilities(g *indexedGraph, nodesByCapability nodesetPerCapability) bfsStateMap {
	var (
		visited = make(bfsStateMap)
		q       []int64
	)
	// Initialize the queue to contain the nodes with a capability.
	for _, nodes := range nodesByCapability {
		for v := range nodes {
			if _, ok := g.safe[v]; ok {
				continue
			}
			q = append(q, v)
			visited[v] = bfsState{}
		}
	}
	// make the search order deterministic
	sort.Slice(q, func(x, y int) bool { return compareFunctions(g.Graph, q[x], q[y]) < 0 })
	// Perform a BFS backwards through the call graph from the interesting
	// nodes.
	for len(q) > 0 {
		v := q[0]
		q = q[1:]
		for _, edge := range g.incomingTo[v] {
			w := edge.GetCaller()
			if _, ok := g.safe[w]; ok {
				continue
			}
			if _, ok := g.allNodesWithExplicitCapability[w]; ok {
				// If edge.Caller is already categorized, we don't want to consider
				// paths that lead from there to another capability.
				continue
			}
			if _, ok := visited[w]; ok {
				// We have already visited w.
				continue
			}
			visited[w] = bfsState{edge: edge}
			q = append(q, w)
		}
	}
	return visited
}

// searchForwardsFromRootFunctions searches from a set of function nodes to
// find all the nodes they can reach which themselves reach a node with some
// capability.
//
// outputNode is called for each node found that can reach a capability.
// outputCall is called for each edge between two such nodes.
// outputCapability is called for each node reached in the graph that has some
// direct capability.
func searchForwardsFromRootFunctions(
	graph *indexedGraph,
	nodesByCapability nodesetPerCapability,
	bfsFromCapabilities bfsStateMap,
	outputNode GraphOutputNodeFn,
	outputCall GraphOutputCallFn,
	outputCapability GraphOutputCapabilityFn,
) {
	var (
		q            []int64
		bfsFromRoots = make(bfsStateMap)
	)
	for v := range bfsFromCapabilities {
		if isRootPackageFunction(graph.Graph, v) {
			q = append(q, v)
			bfsFromRoots[v] = bfsState{}
		}
	}
	// make the search order deterministic
	sort.Slice(q, func(x, y int) bool { return compareFunctions(graph.Graph, q[x], q[y]) < 0 })
	for len(q) > 0 {
		v := q[0]
		q = q[1:]
		if outputNode != nil {
			outputNode(bfsFromRoots, v, bfsFromCapabilities)
		}
		if outputCapability != nil {
			for c, nodes := range nodesByCapability {
				if _, ok := nodes[v]; ok {
					outputCapability(v, c)
				}
			}
		}
		if _, ok := graph.allNodesWithExplicitCapability[v]; ok {
			continue
		}
		edges := graph.outgoingFrom[v]
		for i, edge := range edges {
			if _, ok := bfsFromCapabilities[edge.GetCallee()]; !ok {
				continue
			}
			if i > 0 && edge.GetCallee() == edges[i-1].GetCallee() {
				// We just saw an edge to the same callee, so this edge is redundant.
				continue
			}
			if outputCall != nil {
				outputCall(edge)
			}
			w := edge.GetCallee()
			if _, ok := bfsFromRoots[w]; ok {
				// We have already visited w.
				continue
			}
			bfsFromRoots[w] = bfsState{edge}
			q = append(q, w)
		}
	}
}

// GraphOutputNodeFn represents a function which is called by CapabilityGraph
// for each node.
type GraphOutputNodeFn func(fromRoots bfsStateMap, node int64, toCapability bfsStateMap)

// GraphOutputCallFn represents a function which is called by CapabilityGraph
// for each edge.
type GraphOutputCallFn func(edge *cpb.Graph_Call)

// GraphOutputCapabilityFn represents a function which is called by
// CapabilityGraph for each function capability.
type GraphOutputCapabilityFn func(node int64, c cpb.Capability)

// CapabilityGraph analyzes the callgraph for the packages in pkgs.
//
// It outputs the graph containing all paths from a function belonging
// to one of the root packages in graph to a function which has some
// capability.
//
// outputNode is called for each node in the graph.  Along with the node
// itself, it is passed the state of the BFS search from the root packages,
// and the state of the BFS search from functions with a capability, so that
// the user can reconstruct an example call path including the node.
//
// outputCall is called for each edge between two nodes.
//
// outputCapability is called for each node in the graph that has some
// capability.
//
// If filter is non-nil, it is called once for each capability.  If it returns
// true, then CapabilityGraph generates a call graph for that individual
// capability and calls the relevant output functions, before proceeding to
// the next capability.  If filter is nil, a single graph is generated
// including paths for all capabilities.
func CapabilityGraph(graph *cpb.Graph,
	outputNode GraphOutputNodeFn,
	outputCall GraphOutputCallFn,
	outputCapability GraphOutputCapabilityFn,
	filter func(capability cpb.Capability) bool,
) {
	g := indexGraph(graph)

	search := func(nodesByCapability nodesetPerCapability) {
		bfsFromCapabilities := searchBackwardsFromCapabilities(g, nodesByCapability)

		searchForwardsFromRootFunctions(
			g,
			nodesByCapability,
			bfsFromCapabilities,
			outputNode,
			outputCall,
			outputCapability)
	}
	if filter != nil {
		// Consider each capability individually.
		for c, ns := range g.nodesByCapability {
			if filter(c) {
				search(nodesetPerCapability{c: ns})
			}
		}
	} else {
		// Generate a single graph.
		search(g.nodesByCapability)
	}
}

// ExportGraph processes the specified packages and outputs a callgraph and a
// set of function capability annotations.
//
// The packages in pkgs are "root" packages in the output.  All of their
// transitive dependencies are also included in the output graph.
func ExportGraph(pkgs []*packages.Package, config *Config) *cpb.Graph {
	graph, ssaProg, allFunctions := buildGraph(pkgs, true)
	unsafePointerFunctions := findUnsafePointerConversions(pkgs, ssaProg, allFunctions)
	g := &cpb.Graph{Language: proto.String("Go")}

	// Build g.Modules
	modulePathIndex := make(map[string]*int64)
	{
		pathToModule := make(map[string]*packages.Module)
		forEachPackageIncludingDependencies(pkgs, func(pkg *packages.Package) {
			m := pkg.Module
			if m == nil || m.Path == "" || m.Version == "" {
				// No module information.
				return
			}
			if _, ok := pathToModule[m.Path]; ok {
				// We have seen this path.
				return
			}
			pathToModule[m.Path] = m
		})
		modules := slices.Collect(maps.Values(pathToModule))
		slices.SortFunc(modules, func(a, b *packages.Module) int {
			return strings.Compare(a.Path, b.Path)
		})
		g.Modules = make([]*cpb.Graph_Module, len(modules))
		for i, m := range modules {
			g.Modules[i] = &cpb.Graph_Module{
				Name:    proto.String(m.Path),
				Version: proto.String(m.Version),
			}
			modulePathIndex[m.Path] = proto.Int64(int64(i))
		}
	}

	// Build g.Packages
	pkgIndex := make(map[*types.Package]*int64)
	{
		rootPackagesSet := make(map[*packages.Package]struct{})
		for _, p := range pkgs {
			rootPackagesSet[p] = struct{}{}
		}
		std := standardLibraryPackages()
		type elem struct {
			g *cpb.Graph_Package
			t *types.Package
		}
		var ps []elem
		forEachPackageIncludingDependencies(pkgs, func(pkg *packages.Package) {
			p := &cpb.Graph_Package{
				Name: proto.String(pkg.Name),
				Path: proto.String(pkg.PkgPath),
			}
			if _, ok := rootPackagesSet[pkg]; ok {
				p.IsRoot = proto.Bool(true)
			}
			if _, ok := std[pkg.PkgPath]; ok {
				p.IsStandardLibrary = proto.Bool(true)
			}
			if m := pkg.Module; m != nil {
				p.Module = modulePathIndex[m.Path]
			}
			ps = append(ps, elem{g: p, t: pkg.Types})
		})
		slices.SortFunc(ps, func(a, b elem) int {
			return strings.Compare(a.g.GetPath(), b.g.GetPath())
		})
		g.Packages = make([]*cpb.Graph_Package, len(ps))
		for i, elem := range ps {
			g.Packages[i] = elem.g
			pkgIndex[elem.t] = proto.Int64(int64(i))
		}
	}

	// Build g.Functions
	functionIndex := make(map[*callgraph.Node]*int64)
	{
		type elem struct {
			g *cpb.Graph_Function
			n *callgraph.Node
		}
		var fs []elem
		for fn, node := range graph.Nodes {
			gfn := &cpb.Graph_Function{
				Name: proto.String(fn.String()),
			}
			if o := fn.Origin(); o != nil {
				// Use the origin's name, which won't have the type arguments.
				gfn.Function = proto.String(o.Name())
			} else {
				gfn.Function = proto.String(fn.Name())
			}
			if pkg := nodeToPackage(node); pkg != nil {
				gfn.Package = pkgIndex[pkg]
			}
			if sig := fn.Signature; sig != nil {
				if recv := sig.Recv(); recv != nil {
					if t := recv.Type(); t != nil {
						if ptr, ok := t.(*types.Pointer); ok {
							gfn.Type = proto.String(ptr.Elem().String())
							gfn.Properties = []string{"pointer receiver"}
						} else {
							gfn.Type = proto.String(t.String())
						}
					}
				}
			}
			for _, t := range fn.TypeArgs() {
				gfn.TemplateArguments = append(gfn.TemplateArguments, t.String())
			}
			fs = append(fs, elem{gfn, node})
		}
		slices.SortFunc(fs, func(a, b elem) int {
			return compareFunctionObjects(g, a.g, b.g)
		})
		g.Functions = make([]*cpb.Graph_Function, len(fs))
		for i, elem := range fs {
			g.Functions[i] = elem.g
			functionIndex[elem.n] = proto.Int64(int64(i))
		}
	}

	// Build g.Capabilities
	{
		pTrue := proto.Bool(true)
		for fn, node := range graph.Nodes {
			add := func(c cpb.Capability, implicit bool) {
				fc := &cpb.Graph_FunctionCapability{
					Function:   functionIndex[node],
					Capability: c.Enum(),
				}
				if implicit {
					fc.Implicit = pTrue
				}
				g.Capabilities = append(g.Capabilities, fc)
			}
			if c := getExplicitCapability(fn, config.Classifier); c != cpb.Capability_CAPABILITY_UNSPECIFIED {
				add(c, false)
			} else if !config.DisableBuiltin {
				if usesReflect(fn) {
					add(cpb.Capability_CAPABILITY_REFLECT, true)
				}
				if noSource(fn) {
					add(cpb.Capability_CAPABILITY_ARBITRARY_EXECUTION, true)
				}
				if _, ok := unsafePointerFunctions[fn]; ok {
					add(cpb.Capability_CAPABILITY_UNSAFE_POINTER, true)
				}
			}
		}
	}

	// Build g.Calls
	for _, node := range graph.Nodes {
		idx1, ok := functionIndex[node]
		if !ok {
			continue
		}
		for _, e := range node.Out {
			if !config.Classifier.IncludeCall(e) {
				continue
			}
			idx2, ok := functionIndex[e.Callee]
			if !ok {
				continue
			}
			edge := cpb.Graph_Call{
				Caller: idx1,
				Callee: idx2,
			}
			if position := callsitePosition(e); position.IsValid() {
				edge.CallSite = &cpb.Graph_Site{
					Directory: proto.String(path.Dir(position.Filename)),
					Filename:  proto.String(path.Base(position.Filename)),
					Line:      proto.Int64(int64(position.Line)),
					Column:    proto.Int64(int64(position.Column)),
				}
			}
			g.Calls = append(g.Calls, &edge)
		}
	}
	return g
}

// usesReflect determines if fn copies reflect.Value objects in a way that could
// possibly cause type confusion.
func usesReflect(f *ssa.Function) bool {
	// Find the function variables that do not escape.
	locals := map[ssa.Value]struct{}{}
	for _, l := range f.Locals {
		if !l.Heap {
			locals[l] = struct{}{}
		}
	}
	for _, b := range f.Blocks {
		for _, i := range b.Instrs {
			// An IndexAddr instruction creates an SSA value which refers to an
			// element of an array.  An element of a local array is also local.
			if ia, ok := i.(*ssa.IndexAddr); ok {
				if _, islocal := locals[ia.X]; islocal {
					locals[ia] = struct{}{}
				}
			}
			// A FieldAddr instruction creates an SSA value which refers to a
			// field of a struct.  A field of a local struct is also local.
			if f, ok := i.(*ssa.FieldAddr); ok {
				if _, islocal := locals[f.X]; islocal {
					locals[f] = struct{}{}
				}
			}
			// Check the destination of store instructions.
			if s, ok := i.(*ssa.Store); ok {
				dest := s.Addr
				if _, islocal := locals[dest]; islocal {
					continue
				}
				// dest.Type should be a types.Pointer pointing to the type of the
				// value that is copied by this instruction.
				typ, ok := types.Unalias(dest.Type()).(*types.Pointer)
				if !ok {
					continue
				}
				if !containsReflectValue(typ.Elem()) {
					continue
				}
				// This is a store to a non-local reflect.Value, or to a non-local
				// object that contains a reflect.Value.
				return true
			}
		}
	}
	return false
}

// noSource returns whether f has no source available, e.g. assembly and
// linkname functions.
func noSource(f *ssa.Function) bool {
	// Exclude synthetic functions, such as those loaded from object files.
	return f != nil && f.Blocks == nil && f.Synthetic == ""
}

// findUnsafePointerConversions uses analysis of the syntax tree to find
// functions which convert unsafe.Pointer values to another type.
func findUnsafePointerConversions(pkgs []*packages.Package, ssaProg *ssa.Program, allFunctions map[*ssa.Function]bool) (unsafePointer map[*ssa.Function]struct{}) {
	// AST nodes corresponding to functions which convert unsafe.Pointer values.
	unsafeFunctionNodes := make(map[ast.Node]struct{})
	// Packages which contain variables that are initialized using
	// unsafe.Pointer conversions.  We will later find the function nodes
	// corresponding to the init functions for these packages.
	packagesWithUnsafePointerUseInInitialization := make(map[*types.Package]struct{})
	forEachPackageIncludingDependencies(pkgs, func(pkg *packages.Package) {
		seenUnsafePointerUseInInitialization := false
		for _, file := range pkg.Syntax {
			vis := visitor{
				unsafeFunctionNodes:                  unsafeFunctionNodes,
				seenUnsafePointerUseInInitialization: &seenUnsafePointerUseInInitialization,
				pkg:                                  pkg,
			}
			ast.Walk(&vis, file)
		}
		if seenUnsafePointerUseInInitialization {
			// One of the files in this package contained an unsafe.Pointer
			// conversion in the initialization expression for a package-scoped
			// variable.
			// We want to find later the *ssa.Package object corresponding to the
			// *packages.Package object we have now.  There is no direct pointer
			// between the two, but each has a pointer to the corresponding
			// *types.Package object, so we store that here.
			packagesWithUnsafePointerUseInInitialization[pkg.Types] = struct{}{}
		}
	})
	// Find the *ssa.Function pointers corresponding to the syntax nodes found
	// above.
	unsafePointerFunctions := make(map[*ssa.Function]struct{})
	for f := range allFunctions {
		if _, ok := unsafeFunctionNodes[f.Syntax()]; ok {
			unsafePointerFunctions[f] = struct{}{}
		}
	}
	for _, pkg := range ssaProg.AllPackages() {
		if _, ok := packagesWithUnsafePointerUseInInitialization[pkg.Pkg]; ok {
			// This package had an unsafe.Pointer conversion in the initialization
			// expression for a package-scoped variable, so we add the package's
			// "init" function to unsafePointerFunctions.
			// There will always be an init function for each package; if one
			// didn't exist in the source, a synthetic one will have been
			// created.
			if f := pkg.Func("init"); f != nil {
				unsafePointerFunctions[f] = struct{}{}
			}
		}
	}
	return unsafePointerFunctions
}

func getExplicitCapability(fn *ssa.Function, classifier Classifier) cpb.Capability {
	if fn == nil {
		return cpb.Capability_CAPABILITY_UNSPECIFIED
	}
	if fn.Package() != nil && fn.Package().Pkg != nil {
		pkg := fn.Package().Pkg.Path()
		name := fn.String()
		return classifier.FunctionCategory(pkg, name)
	}
	origin := fn.Origin()
	if origin == nil || origin.Package() == nil || origin.Package().Pkg == nil {
		return cpb.Capability_CAPABILITY_UNSPECIFIED
	}
	// fn is an instantiation of a generic function.  Get the package
	// name and function name of the generic function, and categorize that
	// instead.
	pkg := origin.Package().Pkg.Path()
	name := origin.String()
	return classifier.FunctionCategory(pkg, name)
}

// forEachPath analyzes the callgraph.
//
// For each capability, a BFS is run to find all functions in root packages
// which have a path in the callgraph to a function with that capability.
//
// fn is called for each of these (capability, function) pairs.  fn is passed
// the capability, a map describing the current state of the BFS, and the node
// in the callgraph representing the function.  fn can use this information
// to reconstruct the path.
func forEachPath(graph *cpb.Graph, fn func(cpb.Capability, bfsStateMap, int64)) {
	g := indexGraph(graph)

	var caps []cpb.Capability
	for cap := range g.nodesByCapability {
		caps = append(caps, cap)
	}
	slices.Sort(caps)
	for _, cap := range caps {
		nodes := g.nodesByCapability[cap]
		var (
			visited = make(bfsStateMap)
			q       []int64 // queue for the BFS
		)
		// Initialize the queue to contain the nodes with the capability.
		for v := range nodes {
			if _, ok := g.safe[v]; ok {
				continue
			}
			q = append(q, v)
			visited[v] = bfsState{}
		}
		sort.Slice(q, func(x, y int) bool { return compareFunctions(graph, q[x], q[y]) < 0 })
		for _, v := range q {
			if isRootPackageFunction(graph, v) {
				// v itself is in a root package.  Call fn here because
				// the BFS below will only call fn for functions that call v
				// directly or transitively.
				fn(cap, visited, v)
			}
		}
		// Perform a BFS backwards through the call graph from the interesting
		// nodes.
		for len(q) > 0 {
			v := q[0]
			q = q[1:]
			for _, edge := range g.incomingTo[v] {
				w := edge.GetCaller()
				if _, ok := g.safe[w]; ok {
					continue
				}
				if _, ok := visited[w]; ok {
					// We have already visited w.
					continue
				}
				if _, ok := g.allNodesWithExplicitCapability[w]; ok {
					// w already has an explicit categorization.
					continue
				}
				visited[w] = bfsState{edge: edge}
				q = append(q, w)
				if isRootPackageFunction(graph, w) {
					fn(cap, visited, w)
				}
			}
		}
	}
}

// indexedGraph contains an input Graph, along with structures indexing the
// data within it.
type indexedGraph struct {
	*cpb.Graph

	// safe is those nodes marked with the SAFE capability.  A safe function
	// does not inherit the capabilities of its callees.
	safe nodeset

	// allNodesWithExplicitCapability is those nodes marked with an "explicit"
	// capability.  These do not inherit the capability of any of their callees.
	// For example, a function to open a file may be marked with the FILES
	// capability, and also call a function with the SYSTEM_CALLS capability.
	// Since the function is marked with an explicit capability FILES, it does
	// not inherit SYSTEM_CALLS from its callee.
	//
	// For functions marked with an "implicit" capability, for example where
	// source code analysis finds that it uses unsafe pointers, the capabilities
	// of its callees are still considered, just as they would for a function
	// with no capabilities of its own.
	allNodesWithExplicitCapability nodeset

	nodesByCapability nodesetPerCapability

	// outgoingFrom and incomingTo contain the graph edges indexed into adjacency
	// lists.  The edge lists are sorted, so that algorithms using them can more
	// easily be made deterministic.
	outgoingFrom adjList
	incomingTo   adjList
}

type adjList [][]*cpb.Graph_Call

func (a adjList) add(v int64, edge *cpb.Graph_Call) {
	a[v] = append(a[v], edge)
}

func indexGraph(g *cpb.Graph) *indexedGraph {
	ig := &indexedGraph{
		Graph:                          g,
		safe:                           make(nodeset),
		allNodesWithExplicitCapability: make(nodeset),
		nodesByCapability:              make(nodesetPerCapability),
		outgoingFrom:                   make(adjList, len(g.Functions)),
		incomingTo:                     make(adjList, len(g.Functions)),
	}
	validFn := func(fn *int64) bool {
		return fn != nil && *fn < int64(len(g.Functions))
	}
	for _, c := range g.Capabilities {
		if c.Capability == nil || !validFn(c.Function) {
			continue
		}
		cap := c.GetCapability()
		fn := c.GetFunction()
		if cap == cpb.Capability_CAPABILITY_SAFE {
			ig.safe[fn] = struct{}{}
			continue
		}
		if !c.GetImplicit() {
			ig.allNodesWithExplicitCapability[fn] = struct{}{}
		}
		ig.nodesByCapability.add(cap, fn)
	}
	for _, edge := range g.Calls {
		if !validFn(edge.Callee) || !validFn(edge.Caller) {
			continue
		}
		ig.incomingTo.add(edge.GetCallee(), edge)
		ig.outgoingFrom.add(edge.GetCaller(), edge)
	}
	for _, es := range ig.incomingTo {
		slices.SortFunc(es, func(a, b *cpb.Graph_Call) int {
			return compareEdges(g, a, b)
		})
	}
	for _, es := range ig.outgoingFrom {
		slices.SortFunc(es, func(a, b *cpb.Graph_Call) int {
			return compareEdges(g, a, b)
		})
	}
	return ig
}

func isRootPackageFunction(g *cpb.Graph, v int64) bool {
	p := g.Functions[v].Package
	if p == nil {
		return false
	}
	return g.Packages[*p].GetIsRoot()
}

// intermediatePackages returns a CapabilityInfo for each unique (P, C) pair
// where there is a call path from a function in one of the root packages
// to a function with capability C, and the call path includes a function in
// package P.
func intermediatePackages(graph *cpb.Graph, config *Config) *cpb.CapabilityInfoList {
	type packageAndCapability struct {
		pkg int64
		cpb.Capability
	}
	seen := make(map[packageAndCapability]*cpb.CapabilityInfo)

	// The function CapabilityGraph will call filter for each capability, and
	// then generate the graph for that capability, calling nodeCallback for
	// each node in that graph.  We store the capability that was passed to
	// filter in a variable, so that it is available to nodeCallback.
	var capability cpb.Capability
	filter := func(c cpb.Capability) bool {
		capability = c
		return config.CapabilitySet.Has(c)
	}

	nodeCallback := func(rootBFS bfsStateMap, node int64, capabilityBFS bfsStateMap) {
		// We have found node in a BFS of the callgraph starting from root packages,
		// and in a BFS of the callgraph searching backwards from functions
		// with capabilities.  So we can construct a path from one to the other
		// through node.
		pkg := graph.Functions[node].Package
		if pkg == nil {
			// This node represents some kind of wrapper function that we don't need
			// to consider.
			return
		}
		pc := packageAndCapability{*pkg, capability}
		if _, ok := seen[pc]; ok {
			// We have already seen this (package, capability) pair.
			return
		}
		ci := cpb.CapabilityInfo{
			Capability:  capability.Enum(),
			PackageDir:  graph.Packages[*pkg].Path,
			PackageName: graph.Packages[*pkg].Name,
		}
		if !config.OmitPaths {
			// Add ci.Path entries for the part of the path leading from a function in
			// pkgs to node, including node itself.
			for v := node; true; {
				e := rootBFS[v].edge
				addFunction(&ci.Path, graph, v, e)
				if e == nil {
					break
				}
				v = e.GetCaller()
			}
			// Reverse the path we have so far, since we visited its nodes in reverse
			// order.
			slices.Reverse(ci.Path)
			// Add ci.Path entries for the part of the path leading from node to a
			// function with a capability.
			for v := node; true; {
				e := capabilityBFS[v].edge
				if e == nil {
					break
				}
				v = e.GetCallee()
				addFunction(&ci.Path, graph, v, e)
			}
		}
		seen[pc] = &ci
	}
	CapabilityGraph(graph, nodeCallback, nil, nil, filter)
	cis := make([]*cpb.CapabilityInfo, 0, len(seen))
	for _, ci := range seen {
		cis = append(cis, ci)
	}
	slices.SortFunc(cis, func(a, b *cpb.CapabilityInfo) int {
		if x, y := a.GetCapability(), b.GetCapability(); x != y {
			return int(x) - int(y)
		}
		return strings.Compare(a.GetPackageDir(), b.GetPackageDir())
	})
	return &cpb.CapabilityInfoList{CapabilityInfo: cis}
}
