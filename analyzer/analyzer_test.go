// Copyright 2023 Google LLC
//
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file or at
// https://developers.google.com/open-source/licenses/bsd

package analyzer

import (
	"fmt"
	"os"
	"reflect"
	"strings"
	"testing"

	"github.com/google/capslock/interesting"
	cpb "github.com/google/capslock/proto"
	"github.com/google/go-cmp/cmp"
	"golang.org/x/tools/go/analysis/analysistest"
	"golang.org/x/tools/go/callgraph"
	"golang.org/x/tools/go/packages"
	"google.golang.org/protobuf/proto"
	"google.golang.org/protobuf/testing/protocmp"
)

var filemap = map[string]string{"testlib/foo.go": `package testlib

import "os"

func Foo() { println(os.Getpid()) }
func Bar() { println(os.Getpid()) }
func A() { B(); C() }
func B() { C() }
func C() { println(os.IsExist(nil)) }
`}

// setup contains common code for loading test packages.
func setup(filemap map[string]string, config *Config, pkg ...string) (graph *cpb.Graph, err error) {
	dir, cleanup, err := analysistest.WriteFiles(filemap)
	if cleanup != nil {
		defer cleanup()
	}
	if err != nil {
		return nil, fmt.Errorf("analysistest.WriteFiles: %w", err)
	}
	env := []string{"GOPATH=" + dir, "GO111MODULE=off", "GOPROXY=off"}
	cfg := &packages.Config{
		Mode: PackagesLoadModeNeeded,
		Dir:  dir,
		Env:  append(os.Environ(), env...),
	}
	pkgs, err := packages.Load(cfg, pkg...)
	if err != nil {
		return nil, fmt.Errorf("packages.Load: %w", err)
	}
	graph = ExportGraph(pkgs, config)
	return graph, nil
}

func TestAnalysis(t *testing.T) {
	t.Run("include paths", func(t *testing.T) { testAnalysis(t, false) })
	t.Run("omit paths", func(t *testing.T) { testAnalysis(t, true) })
}

func testAnalysis(t *testing.T, omitPaths bool) {
	config := &Config{
		Classifier:     interesting.DefaultClassifier(),
		DisableBuiltin: false,
		OmitPaths:      omitPaths,
	}
	graph, err := setup(filemap, config, "testlib")
	if err != nil {
		t.Fatalf("setup: %v", err)
	}
	cil := GetCapabilityInfo(graph, config)
	expected := &cpb.CapabilityInfoList{
		CapabilityInfo: []*cpb.CapabilityInfo{{
			PackageName: proto.String("testlib"),
			Capability:  cpb.Capability_CAPABILITY_READ_SYSTEM_STATE.Enum(),
			DepPath:     proto.String("testlib.Bar os.Getpid"),
			Path: []*cpb.Function{
				&cpb.Function{Name: proto.String("testlib.Bar"), Package: proto.String("testlib")},
				&cpb.Function{Name: proto.String("os.Getpid"), Package: proto.String("os")},
			},
			PackageDir:     proto.String("testlib"),
			CapabilityType: cpb.CapabilityType_CAPABILITY_TYPE_DIRECT.Enum(),
		}, {
			PackageName: proto.String("testlib"),
			Capability:  cpb.Capability_CAPABILITY_READ_SYSTEM_STATE.Enum(),
			DepPath:     proto.String("testlib.Foo os.Getpid"),
			Path: []*cpb.Function{
				&cpb.Function{Name: proto.String("testlib.Foo"), Package: proto.String("testlib")},
				&cpb.Function{Name: proto.String("os.Getpid"), Package: proto.String("os")},
			},
			PackageDir:     proto.String("testlib"),
			CapabilityType: cpb.CapabilityType_CAPABILITY_TYPE_DIRECT.Enum(),
		}},
	}
	if omitPaths {
		for _, ci := range expected.CapabilityInfo {
			ci.DepPath = nil
			ci.Path = ci.Path[:1]
		}
	}
	opts := []cmp.Option{
		protocmp.Transform(),
		protocmp.IgnoreFields(&cpb.CapabilityInfoList{}, "package_info"),
		protocmp.IgnoreFields(&cpb.Function{}, "site"),
		protocmp.IgnoreFields(&cpb.Function_Site{}, "filename"),
		protocmp.IgnoreFields(&cpb.Function_Site{}, "line"),
		protocmp.IgnoreFields(&cpb.Function_Site{}, "column"),
	}
	if diff := cmp.Diff(expected, cil, opts...); diff != "" {
		t.Errorf("GetCapabilityInfo(%v): got %v, want %v; diff %s",
			filemap, cil, expected, diff)
	}
}

func TestGraph(t *testing.T) {
	config := &Config{
		Classifier:     interesting.DefaultClassifier(),
		DisableBuiltin: false,
	}
	graph, err := setup(filemap, config, "testlib")
	if err != nil {
		t.Fatalf("setup: %v", err)
	}
	nodes := make(map[string]struct{})
	calls := make(map[[2]string]struct{})
	caps := make(map[string][]cpb.Capability)
	functionName := func(node int64) string {
		return graph.Functions[node].GetName()
	}
	CapabilityGraph(
		graph,
		func(_ bfsStateMap, node int64, _ bfsStateMap) {
			nodes[functionName(node)] = struct{}{}
		},
		func(edge *cpb.Graph_Call) {
			calls[[2]string{functionName(edge.GetCaller()), functionName(edge.GetCallee())}] = struct{}{}
		},
		func(node int64, c cpb.Capability) {
			f := functionName(node)
			caps[f] = append(caps[f], c)
		},
		nil)
	expectedNodes := map[string]struct{}{
		"testlib.Foo": {},
		"testlib.Bar": {},
		"os.Getpid":   {},
	}
	expectedCalls := map[[2]string]struct{}{
		{"testlib.Foo", "os.Getpid"}: {},
		{"testlib.Bar", "os.Getpid"}: {},
	}
	expectedCaps := map[string][]cpb.Capability{
		"os.Getpid": {cpb.Capability_CAPABILITY_READ_SYSTEM_STATE},
	}
	if !reflect.DeepEqual(nodes, expectedNodes) {
		t.Errorf("CapabilityGraph(%v): got nodes %v want %v",
			filemap, nodes, expectedNodes)
	}
	if !reflect.DeepEqual(calls, expectedCalls) {
		t.Errorf("CapabilityGraph(%v): got calls %v want %v",
			filemap, calls, expectedCalls)
	}
	if !reflect.DeepEqual(caps, expectedCaps) {
		t.Errorf("CapabilityGraph(%v): got capabilities %v want %v",
			filemap, caps, expectedCaps)
	}
}

// testClassifier is used for testing that non-default classifiers work
// correctly.
type testClassifier struct {
	// functions is a map from {package name, function name} to the capability
	// the classifier should return.
	functions map[[2]string]cpb.Capability
	// ignoredEdges is a set of {caller, callee} pairs denoting callgraph edges
	// the classifier thinks should be ignored.
	ignoredEdges map[[2]string]struct{}
}

func (t *testClassifier) FunctionCategory(pkg string, name string) cpb.Capability {
	return t.functions[[2]string{pkg, name}]
}

func (t *testClassifier) IncludeCall(edge *callgraph.Edge) bool {
	caller := edge.Caller.Func.String()
	callee := edge.Callee.Func.String()
	_, ignore := t.ignoredEdges[[2]string{caller, callee}]
	return !ignore
}

var testClassifier1 = testClassifier{
	// Only categorize os.IsExist as having a capability.
	functions: map[[2]string]cpb.Capability{
		{"os", "os.IsExist"}: cpb.Capability_CAPABILITY_FILES,
	},
	// Exclude calls from A to C.
	ignoredEdges: map[[2]string]struct{}{
		{"testlib.A", "testlib.C"}: struct{}{},
	},
}

func TestAnalysisWithClassifier(t *testing.T) {
	config := &Config{
		Classifier:     &testClassifier1,
		DisableBuiltin: true,
	}
	graph, err := setup(filemap, config, "testlib")
	if err != nil {
		t.Fatalf("setup: %v", err)
	}
	cil := GetCapabilityInfo(graph, config)
	expected := &cpb.CapabilityInfoList{
		CapabilityInfo: []*cpb.CapabilityInfo{{
			PackageName: proto.String("testlib"),
			Capability:  cpb.Capability_CAPABILITY_FILES.Enum(),
			Path: []*cpb.Function{
				&cpb.Function{Name: proto.String("testlib.A"), Package: proto.String("testlib")},
				&cpb.Function{Name: proto.String("testlib.B"), Package: proto.String("testlib")},
				&cpb.Function{Name: proto.String("testlib.C"), Package: proto.String("testlib")},
				&cpb.Function{Name: proto.String("os.IsExist"), Package: proto.String("os")},
			},
			PackageDir:     proto.String("testlib"),
			CapabilityType: cpb.CapabilityType_CAPABILITY_TYPE_DIRECT.Enum(),
		}, {
			PackageName: proto.String("testlib"),
			Capability:  cpb.Capability_CAPABILITY_FILES.Enum(),
			Path: []*cpb.Function{
				&cpb.Function{Name: proto.String("testlib.B"), Package: proto.String("testlib")},
				&cpb.Function{Name: proto.String("testlib.C"), Package: proto.String("testlib")},
				&cpb.Function{Name: proto.String("os.IsExist"), Package: proto.String("os")},
			},
			PackageDir:     proto.String("testlib"),
			CapabilityType: cpb.CapabilityType_CAPABILITY_TYPE_DIRECT.Enum(),
		}, {
			PackageName: proto.String("testlib"),
			Capability:  cpb.Capability_CAPABILITY_FILES.Enum(),
			Path: []*cpb.Function{
				&cpb.Function{Name: proto.String("testlib.C"), Package: proto.String("testlib")},
				&cpb.Function{Name: proto.String("os.IsExist"), Package: proto.String("os")},
			},
			PackageDir:     proto.String("testlib"),
			CapabilityType: cpb.CapabilityType_CAPABILITY_TYPE_DIRECT.Enum(),
		}},
	}
	opts := []cmp.Option{
		protocmp.Transform(),
		protocmp.SortRepeated(func(a, b *cpb.CapabilityInfo) bool {
			return a.GetDepPath() < b.GetDepPath()
		}),
		protocmp.IgnoreFields(&cpb.CapabilityInfoList{}, "package_info"),
		protocmp.IgnoreFields(&cpb.CapabilityInfo{}, "dep_path"),
		protocmp.IgnoreFields(&cpb.Function{}, "site"),
		protocmp.IgnoreFields(&cpb.Function_Site{}, "filename"),
		protocmp.IgnoreFields(&cpb.Function_Site{}, "line"),
		protocmp.IgnoreFields(&cpb.Function_Site{}, "column"),
	}
	if diff := cmp.Diff(expected, cil, opts...); diff != "" {
		t.Errorf("GetCapabilityInfo(%v): got %v, want %v; diff %s",
			filemap, cil, expected, diff)
	}
}

func TestGraphWithClassifier(t *testing.T) {
	config := &Config{
		Classifier:     &testClassifier1,
		DisableBuiltin: true,
	}
	graph, err := setup(filemap, config, "testlib")
	if err != nil {
		t.Fatalf("setup: %v", err)
	}
	nodes := make(map[string]struct{})
	calls := make(map[[2]string]struct{})
	caps := make(map[string][]cpb.Capability)
	functionName := func(node int64) string {
		return graph.Functions[node].GetName()
	}
	CapabilityGraph(
		graph,
		func(_ bfsStateMap, node int64, _ bfsStateMap) {
			nodes[functionName(node)] = struct{}{}
		},
		func(edge *cpb.Graph_Call) {
			calls[[2]string{functionName(edge.GetCaller()), functionName(edge.GetCallee())}] = struct{}{}
		},
		func(node int64, c cpb.Capability) {
			name := functionName(node)
			caps[name] = append(caps[name], c)
		},
		nil)
	expectedNodes := map[string]struct{}{
		"testlib.A":  {},
		"testlib.B":  {},
		"testlib.C":  {},
		"os.IsExist": {},
	}
	expectedCalls := map[[2]string]struct{}{
		{"testlib.A", "testlib.B"}:  {},
		{"testlib.B", "testlib.C"}:  {},
		{"testlib.C", "os.IsExist"}: {},
	}
	expectedCaps := map[string][]cpb.Capability{
		"os.IsExist": {cpb.Capability_CAPABILITY_FILES},
	}
	if !reflect.DeepEqual(nodes, expectedNodes) {
		t.Errorf("CapabilityGraph(%v): got nodes %v want %v",
			filemap, nodes, expectedNodes)
	}
	if !reflect.DeepEqual(calls, expectedCalls) {
		t.Errorf("CapabilityGraph(%v): got calls %v want %v",
			filemap, calls, expectedCalls)
	}
	if !reflect.DeepEqual(caps, expectedCaps) {
		t.Errorf("CapabilityGraph(%v): got capabilities %v want %v",
			filemap, caps, expectedCaps)
	}
}

func TestAnalysisPackageGranularity(t *testing.T) {
	config := &Config{
		Classifier:     interesting.DefaultClassifier(),
		DisableBuiltin: false,
		Granularity:    GranularityPackage,
	}
	graph, err := setup(filemap, config, "testlib")
	if err != nil {
		t.Fatalf("setup: %v", err)
	}
	cil := GetCapabilityInfo(graph, config)
	expected := &cpb.CapabilityInfoList{
		CapabilityInfo: []*cpb.CapabilityInfo{{
			PackageName: proto.String("testlib"),
			Capability:  cpb.Capability_CAPABILITY_READ_SYSTEM_STATE.Enum(),
			Path: []*cpb.Function{
				&cpb.Function{Name: proto.String("testlib.Bar"), Package: proto.String("testlib")},
				&cpb.Function{Name: proto.String("os.Getpid"), Package: proto.String("os")},
			},
			PackageDir:     proto.String("testlib"),
			CapabilityType: cpb.CapabilityType_CAPABILITY_TYPE_DIRECT.Enum(),
		}},
	}
	opts := []cmp.Option{
		protocmp.Transform(),
		protocmp.IgnoreFields(&cpb.CapabilityInfoList{}, "package_info"),
		protocmp.IgnoreFields(&cpb.CapabilityInfo{}, "dep_path"),
		protocmp.IgnoreFields(&cpb.Function{}, "site"),
		protocmp.IgnoreFields(&cpb.Function_Site{}, "filename"),
		protocmp.IgnoreFields(&cpb.Function_Site{}, "line"),
		protocmp.IgnoreFields(&cpb.Function_Site{}, "column"),
	}
	if diff := cmp.Diff(expected, cil, opts...); diff != "" {
		t.Errorf("GetCapabilityInfo(%v): got %v, want %v; diff %s",
			filemap, cil, expected, diff)
	}
}

func TestNewCapabilitySet(t *testing.T) {
	for _, test := range []struct {
		list             string
		wantCapabilities map[cpb.Capability]struct{}
		wantNegated      bool
	}{
		{
			list: "NETWORK",
			wantCapabilities: map[cpb.Capability]struct{}{
				cpb.Capability_CAPABILITY_NETWORK: struct{}{},
			},
			wantNegated: false,
		},
		{
			list:             "",
			wantCapabilities: nil,
			wantNegated:      true,
		},
		{
			list: "-NETWORK",
			wantCapabilities: map[cpb.Capability]struct{}{
				cpb.Capability_CAPABILITY_NETWORK: struct{}{},
			},
			wantNegated: true,
		},
		{
			list: "CAPABILITY_NETWORK",
			wantCapabilities: map[cpb.Capability]struct{}{
				cpb.Capability_CAPABILITY_NETWORK: struct{}{},
			},
			wantNegated: false,
		},
		{
			list: "NETWORK,FILES",
			wantCapabilities: map[cpb.Capability]struct{}{
				cpb.Capability_CAPABILITY_NETWORK: struct{}{},
				cpb.Capability_CAPABILITY_FILES:   struct{}{},
			},
			wantNegated: false,
		},
		{
			list: "-NETWORK,-CAPABILITY_FILES",
			wantCapabilities: map[cpb.Capability]struct{}{
				cpb.Capability_CAPABILITY_NETWORK: struct{}{},
				cpb.Capability_CAPABILITY_FILES:   struct{}{},
			},
			wantNegated: true,
		},
		{
			list: "CAPABILITY_FILES,CAPABILITY_NETWORK,CAPABILITY_RUNTIME,CAPABILITY_READ_SYSTEM_STATE,CAPABILITY_MODIFY_SYSTEM_STATE,CAPABILITY_OPERATING_SYSTEM,CAPABILITY_SYSTEM_CALLS,CAPABILITY_ARBITRARY_EXECUTION,CAPABILITY_CGO,CAPABILITY_UNANALYZED,CAPABILITY_UNSAFE_POINTER,CAPABILITY_REFLECT,CAPABILITY_EXEC",
			wantCapabilities: map[cpb.Capability]struct{}{
				cpb.Capability_CAPABILITY_FILES:               struct{}{},
				cpb.Capability_CAPABILITY_NETWORK:             struct{}{},
				cpb.Capability_CAPABILITY_RUNTIME:             struct{}{},
				cpb.Capability_CAPABILITY_READ_SYSTEM_STATE:   struct{}{},
				cpb.Capability_CAPABILITY_MODIFY_SYSTEM_STATE: struct{}{},
				cpb.Capability_CAPABILITY_OPERATING_SYSTEM:    struct{}{},
				cpb.Capability_CAPABILITY_SYSTEM_CALLS:        struct{}{},
				cpb.Capability_CAPABILITY_ARBITRARY_EXECUTION: struct{}{},
				cpb.Capability_CAPABILITY_CGO:                 struct{}{},
				cpb.Capability_CAPABILITY_UNANALYZED:          struct{}{},
				cpb.Capability_CAPABILITY_UNSAFE_POINTER:      struct{}{},
				cpb.Capability_CAPABILITY_REFLECT:             struct{}{},
				cpb.Capability_CAPABILITY_EXEC:                struct{}{},
			},
			wantNegated: false,
		},
	} {
		cs, err := NewCapabilitySet(test.list)
		if err != nil {
			t.Errorf("NewCapabilitySet(%q): got err == %v, want nil error",
				test.list, err)
			continue
		}
		if test.wantCapabilities == nil {
			if cs != nil {
				t.Errorf("NewCapabilitySet(%q): got non-nil, want nil", test.list)
			}
			continue
		}
		if !reflect.DeepEqual(cs.capabilities, test.wantCapabilities) {
			t.Errorf("NewCapabilitySet(%q): got capabilities %v want %v",
				test.list, cs.capabilities, test.wantCapabilities)
		}
		if cs.negated != test.wantNegated {
			t.Errorf("NewCapabilitySet(%q): got negated = %v want %v",
				test.list, cs.negated, test.wantNegated)
		}
	}
	for _, list := range []string{
		"NOTWORK",
		"FILES!",
		"NETWORKFILES",
		"-NETWORK,FILES",
		"NETWORK,-FILES",
		",NETWORK",
		"NETWORK,",
		"NETWORK,,FILES",
		",",
		",,",
		"\x00",
	} {
		_, err := NewCapabilitySet(list)
		if err == nil {
			t.Errorf("NewCapabilitySet(%q): got err == nil, want error", list)
		}
	}
}

func TestIntermediatePackages(t *testing.T) {
	filemap := map[string]string{
		"p1/p1.go": `package p1; func Foo() { Bar() }; func Bar() { }`,
		"p2/p2.go": `package p2; import "p1"; func Foo() { p1.Foo() }`,
		"p3/p3.go": `package p3; import "p1"; func Foo() { p1.Foo() }; func Bar() { p1.Bar() }`,
		"p4/p4.go": `package p4; import "p2"; import "p3"; func Foo() { p2.Foo(); p3.Foo(); p3.Bar() }; func Bar() { }`,
	}
	classifier := testClassifier{
		functions: map[[2]string]cpb.Capability{
			{"p1", "p1.Foo"}: cpb.Capability_CAPABILITY_FILES,
			{"p1", "p1.Bar"}: cpb.Capability_CAPABILITY_MODIFY_SYSTEM_STATE,
			{"p4", "p4.Bar"}: cpb.Capability_CAPABILITY_READ_SYSTEM_STATE,
		},
		ignoredEdges: nil,
	}
	config := &Config{
		Classifier:     &classifier,
		DisableBuiltin: true,
		Granularity:    GranularityIntermediate,
	}
	graph, err := setup(filemap, config, "p4")
	if err != nil {
		t.Fatalf("setup: %v", err)
	}
	for _, test := range []struct {
		capabilities string
		expected     *cpb.CapabilityInfoList
	}{
		{
			capabilities: "", // all
			expected: &cpb.CapabilityInfoList{
				CapabilityInfo: []*cpb.CapabilityInfo{
					{
						PackageName: proto.String("p1"),
						Capability:  cpb.Capability_CAPABILITY_FILES.Enum(),
						Path: []*cpb.Function{
							&cpb.Function{Name: proto.String("p4.Foo"), Package: proto.String("p4")},
							&cpb.Function{Name: proto.String("p2.Foo"), Package: proto.String("p2")},
							&cpb.Function{Name: proto.String("p1.Foo"), Package: proto.String("p1")},
						},
						PackageDir: proto.String("p1"),
					},
					{
						PackageName: proto.String("p2"),
						Capability:  cpb.Capability_CAPABILITY_FILES.Enum(),
						Path: []*cpb.Function{
							&cpb.Function{Name: proto.String("p4.Foo"), Package: proto.String("p4")},
							&cpb.Function{Name: proto.String("p2.Foo"), Package: proto.String("p2")},
							&cpb.Function{Name: proto.String("p1.Foo"), Package: proto.String("p1")},
						},
						PackageDir: proto.String("p2"),
					},
					{
						PackageName: proto.String("p3"),
						Capability:  cpb.Capability_CAPABILITY_FILES.Enum(),
						Path: []*cpb.Function{
							&cpb.Function{Name: proto.String("p4.Foo"), Package: proto.String("p4")},
							&cpb.Function{Name: proto.String("p3.Foo"), Package: proto.String("p3")},
							&cpb.Function{Name: proto.String("p1.Foo"), Package: proto.String("p1")},
						},
						PackageDir: proto.String("p3"),
					},
					{
						PackageName: proto.String("p4"),
						Capability:  cpb.Capability_CAPABILITY_FILES.Enum(),
						Path: []*cpb.Function{
							&cpb.Function{Name: proto.String("p4.Foo"), Package: proto.String("p4")},
							&cpb.Function{Name: proto.String("p2.Foo"), Package: proto.String("p2")},
							&cpb.Function{Name: proto.String("p1.Foo"), Package: proto.String("p1")},
						},
						PackageDir: proto.String("p4"),
					},
					{
						PackageName: proto.String("p4"),
						Capability:  cpb.Capability_CAPABILITY_READ_SYSTEM_STATE.Enum(),
						Path: []*cpb.Function{
							&cpb.Function{Name: proto.String("p4.Bar"), Package: proto.String("p4")},
						},
						PackageDir: proto.String("p4"),
					},
					{
						PackageName: proto.String("p1"),
						Capability:  cpb.Capability_CAPABILITY_MODIFY_SYSTEM_STATE.Enum(),
						Path: []*cpb.Function{
							&cpb.Function{Name: proto.String("p4.Foo"), Package: proto.String("p4")},
							&cpb.Function{Name: proto.String("p3.Bar"), Package: proto.String("p3")},
							&cpb.Function{Name: proto.String("p1.Bar"), Package: proto.String("p1")},
						},
						PackageDir: proto.String("p1"),
					},
					{
						PackageName: proto.String("p3"),
						Capability:  cpb.Capability_CAPABILITY_MODIFY_SYSTEM_STATE.Enum(),
						Path: []*cpb.Function{
							&cpb.Function{Name: proto.String("p4.Foo"), Package: proto.String("p4")},
							&cpb.Function{Name: proto.String("p3.Bar"), Package: proto.String("p3")},
							&cpb.Function{Name: proto.String("p1.Bar"), Package: proto.String("p1")},
						},
						PackageDir: proto.String("p3"),
					},
					{
						PackageName: proto.String("p4"),
						Capability:  cpb.Capability_CAPABILITY_MODIFY_SYSTEM_STATE.Enum(),
						Path: []*cpb.Function{
							&cpb.Function{Name: proto.String("p4.Foo"), Package: proto.String("p4")},
							&cpb.Function{Name: proto.String("p3.Bar"), Package: proto.String("p3")},
							&cpb.Function{Name: proto.String("p1.Bar"), Package: proto.String("p1")},
						},
						PackageDir: proto.String("p4"),
					},
				},
			},
		},
		{
			capabilities: "READ_SYSTEM_STATE",
			expected: &cpb.CapabilityInfoList{
				CapabilityInfo: []*cpb.CapabilityInfo{
					{
						PackageName: proto.String("p4"),
						Capability:  cpb.Capability_CAPABILITY_READ_SYSTEM_STATE.Enum(),
						Path: []*cpb.Function{
							&cpb.Function{Name: proto.String("p4.Bar"), Package: proto.String("p4")},
						},
						PackageDir: proto.String("p4"),
					},
				},
			},
		},
	} {
		cs, err := NewCapabilitySet(test.capabilities)
		if err != nil {
			t.Fatalf("NewCapabilitySet(%q): %v", test.capabilities, err)
		}
		config.CapabilitySet = cs
		cil := GetCapabilityInfo(graph, config)
		opts := []cmp.Option{
			protocmp.Transform(),
			protocmp.SortRepeated(func(a, b *cpb.CapabilityInfo) bool {
				if u, v := a.GetCapability(), b.GetCapability(); u != v {
					return u < v
				}
				return a.GetPackageDir() < b.GetPackageDir()
			}),
			protocmp.IgnoreFields(&cpb.CapabilityInfoList{}, "package_info"),
			protocmp.IgnoreFields(&cpb.CapabilityInfo{}, "dep_path"),
			protocmp.IgnoreFields(&cpb.CapabilityInfo{}, "capability_type"),
			protocmp.IgnoreFields(&cpb.Function{}, "site"),
			protocmp.IgnoreFields(&cpb.Function_Site{}, "filename"),
			protocmp.IgnoreFields(&cpb.Function_Site{}, "line"),
			protocmp.IgnoreFields(&cpb.Function_Site{}, "column"),
		}
		if diff := cmp.Diff(test.expected, cil, opts...); diff != "" {
			t.Errorf("GetCapabilityInfo: got %v, want %v; diff %s",
				cil, test.expected, diff)
		}
	}
}

func TestAlias(t *testing.T) {
	filemap := map[string]string{
		"p1/p1.go": `package p1; func Foo() { }; type T struct {}; func (t T) M() { Foo() }`,
		"p2/p2.go": `package p2; import "p1"; func Foo() { type t = p1.T; m := t.M; m(t{}); }`,
	}
	classifier := testClassifier{
		functions: map[[2]string]cpb.Capability{
			{"p1", "p1.Foo"}: cpb.Capability_CAPABILITY_FILES,
		},
		ignoredEdges: nil,
	}
	config := &Config{
		Classifier:     &classifier,
		DisableBuiltin: true,
	}
	graph, err := setup(filemap, config, "p2")
	if err != nil {
		t.Fatalf("setup: %v", err)
	}
	expected := &cpb.CapabilityInfoList{
		CapabilityInfo: []*cpb.CapabilityInfo{
			{
				PackageName: proto.String("p2"),
				Capability:  cpb.Capability_CAPABILITY_FILES.Enum(),
				Path: []*cpb.Function{
					&cpb.Function{Name: proto.String("p2.Foo"), Package: proto.String("p2")},
					&cpb.Function{Name: proto.String("(p2.t).M$thunk"), Package: proto.String("p1")},
					&cpb.Function{Name: proto.String("(p1.T).M"), Package: proto.String("p1")},
					&cpb.Function{Name: proto.String("p1.Foo"), Package: proto.String("p1")},
				},
				PackageDir: proto.String("p2"),
			},
		},
	}

	cil := GetCapabilityInfo(graph, config)
	opts := []cmp.Option{
		protocmp.Transform(),
		protocmp.SortRepeated(func(a, b *cpb.CapabilityInfo) bool {
			if u, v := a.GetCapability(), b.GetCapability(); u != v {
				return u < v
			}
			return a.GetPackageDir() < b.GetPackageDir()
		}),
		protocmp.IgnoreFields(&cpb.CapabilityInfoList{}, "package_info"),
		protocmp.IgnoreFields(&cpb.CapabilityInfo{}, "dep_path"),
		protocmp.IgnoreFields(&cpb.CapabilityInfo{}, "capability_type"),
		protocmp.IgnoreFields(&cpb.Function{}, "site"),
		protocmp.IgnoreFields(&cpb.Function_Site{}, "filename"),
		protocmp.IgnoreFields(&cpb.Function_Site{}, "line"),
		protocmp.IgnoreFields(&cpb.Function_Site{}, "column"),
	}
	if diff := cmp.Diff(expected, cil, opts...); diff != "" {
		t.Errorf("GetCapabilityInfo: got %v, want %v; diff %s", cil, expected, diff)
	}
}

func TestExportGraph(t *testing.T) {
	filemap := map[string]string{"testlib/foo.go": `package testlib
		import "unsafe"
		type T int
		func (t T) M() {}
		func Foo() { Bar() }
		func Bar() { T(3).M(); Baz(6); Baz("") }
		func Baz[T interface{int | string}](a T) {
			println(a)
		}
		func UP() {
			var u unsafe.Pointer
			println(*(*int)(u))
		}
	`}
	classifier := &testClassifier{
		functions: map[[2]string]cpb.Capability{
			{"testlib", "testlib.Foo"}: cpb.Capability_CAPABILITY_FILES,
		},
	}
	config := &Config{Classifier: classifier}
	graph, err := setup(filemap, config, "testlib")
	if err != nil {
		t.Fatalf("setup: %v", err)
	}
	expected := &cpb.Graph{
		Language: proto.String("Go"),
		Functions: []*cpb.Graph_Function{
			{
				Name:     proto.String("testlib.Bar"),
				Package:  proto.Int64(0),
				Function: proto.String("Bar"),
			},
			{
				Name:     proto.String("testlib.Baz"),
				Package:  proto.Int64(0),
				Function: proto.String("Baz"),
			},
			{
				Name:          proto.String("testlib.Baz[int]"),
				Package:       proto.Int64(0),
				Function:      proto.String("Baz[int]"),
				TypeArguments: []string{"int"},
			},
			{
				Name:          proto.String("testlib.Baz[string]"),
				Package:       proto.Int64(0),
				Function:      proto.String("Baz[string]"),
				TypeArguments: []string{"string"},
			},
			{
				Name:     proto.String("testlib.Foo"),
				Package:  proto.Int64(0),
				Function: proto.String("Foo"),
			},
			{
				Name:     proto.String("testlib.UP"),
				Package:  proto.Int64(0),
				Function: proto.String("UP"),
			},
			{
				Name:     proto.String("testlib.init"),
				Package:  proto.Int64(0),
				Function: proto.String("init"),
			},
			{
				Name:     proto.String("(*testlib.T).M"),
				Package:  proto.Int64(0),
				Type:     proto.String("*testlib.T"),
				Function: proto.String("M"),
			},
			{
				Name:     proto.String("(testlib.T).M"),
				Package:  proto.Int64(0),
				Type:     proto.String("testlib.T"),
				Function: proto.String("M"),
			},
			{
				Name:     proto.String("unsafe.init"),
				Package:  proto.Int64(1),
				Function: proto.String("init"),
			},
		},
		Calls: []*cpb.Graph_Call{
			{
				Caller: proto.Int64(0),
				Callee: proto.Int64(2),
				CallSite: &cpb.Graph_Site{
					Filename: proto.String("foo.go"),
					Line:     proto.Int64(6),
					Column:   proto.Int64(29),
				},
			},
			{
				Caller: proto.Int64(0),
				Callee: proto.Int64(3),
				CallSite: &cpb.Graph_Site{
					Filename: proto.String("foo.go"),
					Line:     proto.Int64(6),
					Column:   proto.Int64(37),
				},
			},
			{
				Caller: proto.Int64(0),
				Callee: proto.Int64(8),
				CallSite: &cpb.Graph_Site{
					Filename: proto.String("foo.go"),
					Line:     proto.Int64(6),
					Column:   proto.Int64(22),
				},
			},
			{
				Caller: proto.Int64(4),
				Callee: proto.Int64(0),
				CallSite: &cpb.Graph_Site{
					Filename: proto.String("foo.go"),
					Line:     proto.Int64(5),
					Column:   proto.Int64(19),
				},
			},
			{
				Caller: proto.Int64(6),
				Callee: proto.Int64(9),
			},
			{
				Caller: proto.Int64(7),
				Callee: proto.Int64(8),
			},
		},
		Capabilities: []*cpb.Graph_FunctionCapability{
			{
				Function:   proto.Int64(4),
				Capability: cpb.Capability_CAPABILITY_FILES.Enum(),
			},
			{
				Function:   proto.Int64(5),
				Capability: cpb.Capability_CAPABILITY_UNSAFE_POINTER.Enum(),
				Implicit:   proto.Bool(true),
			},
		},
		Packages: []*cpb.Graph_Package{
			{
				Name:   proto.String("testlib"),
				Path:   proto.String("testlib"),
				IsRoot: proto.Bool(true),
			},
			{
				Name:              proto.String("unsafe"),
				Path:              proto.String("unsafe"),
				IsStandardLibrary: proto.Bool(true),
			},
		},
	}
	opts := []cmp.Option{
		protocmp.Transform(),
		protocmp.IgnoreFields(&cpb.Graph_Site{}, "directory"),
		protocmp.FilterField(&cpb.Graph{}, "calls", protocmp.SortRepeated(func(a, b *cpb.Graph_Call) bool {
			if a.GetCaller() != b.GetCaller() {
				return a.GetCaller() < b.GetCaller()
			}
			return a.GetCallee() < b.GetCallee()
		})),
		protocmp.FilterField(&cpb.Graph{}, "capabilities", protocmp.SortRepeated(func(a, b *cpb.Graph_FunctionCapability) bool {
			if a.GetFunction() != b.GetFunction() {
				return a.GetFunction() < b.GetFunction()
			}
			return a.GetCapability() < b.GetCapability()
		})),
	}
	if diff := cmp.Diff(expected, graph, opts...); diff != "" {
		t.Errorf("ExportGraph: got %v, want %v; diff %s", graph, expected, diff)
	}
}

// TestWrappers tests the analyzer on various types of synthetic wrapper functions.
func TestWrappers(t *testing.T) {
	filemap := map[string]string{
		"p1/p1.go": `package p1; import "p2"
type Embedder struct { p2.Foo }
var I interface { M(); PM() } = new(Embedder)

func CallPromotedMethod() { I.M() }
func CallPromotedPointerMethod() { I.PM() }

func CallPointerReceiverWrapper() {
	f := (*p2.Foo).M
	x := new(p2.Foo)
	f(x)
}

func CallMethodValue() {
	var x p2.Foo
	f := x.M
	f()
}

func CallMethodExpression() {
	f := p2.Foo.M
	var x p2.Foo
	f(x)
}
`,
		"p2/p2.go": `package p2
type Foo struct {}

func (f Foo) M() { Interesting() }
func (f *Foo) PM() { Interesting() }

func Interesting() {}
`,
	}
	classifier := testClassifier{
		functions: map[[2]string]cpb.Capability{
			{"p2", "p2.Interesting"}: cpb.Capability_CAPABILITY_FILES,
		},
		ignoredEdges: nil,
	}
	config := &Config{
		Classifier:     &classifier,
		DisableBuiltin: true,
	}
	graph, err := setup(filemap, config, "p1", "p2")
	if err != nil {
		t.Fatalf("setup: %v", err)
	}
	expected := &cpb.CapabilityInfoList{
		CapabilityInfo: []*cpb.CapabilityInfo{
			{
				PackageName: proto.String("p1"),
				Capability:  cpb.Capability_CAPABILITY_FILES.Enum(),
				Path: []*cpb.Function{
					&cpb.Function{Name: proto.String("p1.CallMethodExpression"), Package: proto.String("p1")},
					&cpb.Function{Name: proto.String("(p2.Foo).M$thunk"), Package: proto.String("p2")},
					&cpb.Function{Name: proto.String("(p2.Foo).M"), Package: proto.String("p2")},
					&cpb.Function{Name: proto.String("p2.Interesting"), Package: proto.String("p2")},
				},
				PackageDir: proto.String("p1"),
			},
			{
				PackageName: proto.String("p1"),
				Capability:  cpb.Capability_CAPABILITY_FILES.Enum(),
				Path: []*cpb.Function{
					&cpb.Function{Name: proto.String("p1.CallMethodValue"), Package: proto.String("p1")},
					&cpb.Function{Name: proto.String("(p2.Foo).M$bound"), Package: proto.String("p2")},
					&cpb.Function{Name: proto.String("(p2.Foo).M"), Package: proto.String("p2")},
					&cpb.Function{Name: proto.String("p2.Interesting"), Package: proto.String("p2")},
				},
				PackageDir: proto.String("p1"),
			},
			{
				PackageName: proto.String("p1"),
				Capability:  cpb.Capability_CAPABILITY_FILES.Enum(),
				Path: []*cpb.Function{
					&cpb.Function{Name: proto.String("p1.CallPointerReceiverWrapper"), Package: proto.String("p1")},
					&cpb.Function{Name: proto.String("(*p2.Foo).M$thunk"), Package: proto.String("p2")},
					&cpb.Function{Name: proto.String("(p2.Foo).M"), Package: proto.String("p2")},
					&cpb.Function{Name: proto.String("p2.Interesting"), Package: proto.String("p2")},
				},
				PackageDir: proto.String("p1"),
			},
			{
				PackageName: proto.String("p1"),
				Capability:  cpb.Capability_CAPABILITY_FILES.Enum(),
				Path: []*cpb.Function{
					&cpb.Function{Name: proto.String("p1.CallPromotedMethod"), Package: proto.String("p1")},
					&cpb.Function{Name: proto.String("(*p1.Embedder).M"), Package: proto.String("p1")},
					&cpb.Function{Name: proto.String("(p2.Foo).M"), Package: proto.String("p2")},
					&cpb.Function{Name: proto.String("p2.Interesting"), Package: proto.String("p2")},
				},
				PackageDir: proto.String("p1"),
			},
			{
				PackageName: proto.String("p1"),
				Capability:  cpb.Capability_CAPABILITY_FILES.Enum(),
				Path: []*cpb.Function{
					&cpb.Function{Name: proto.String("p1.CallPromotedPointerMethod"), Package: proto.String("p1")},
					&cpb.Function{Name: proto.String("(*p1.Embedder).PM"), Package: proto.String("p1")},
					&cpb.Function{Name: proto.String("(*p2.Foo).PM"), Package: proto.String("p2")},
					&cpb.Function{Name: proto.String("p2.Interesting"), Package: proto.String("p2")},
				},
				PackageDir: proto.String("p1"),
			},
			{
				PackageName: proto.String("p1"),
				Capability:  cpb.Capability_CAPABILITY_FILES.Enum(),
				Path: []*cpb.Function{
					&cpb.Function{Name: proto.String("(p1.Embedder).M"), Package: proto.String("p1")},
					&cpb.Function{Name: proto.String("(p2.Foo).M"), Package: proto.String("p2")},
					&cpb.Function{Name: proto.String("p2.Interesting"), Package: proto.String("p2")},
				},
				PackageDir: proto.String("p1"),
			},
			{
				PackageName: proto.String("p1"),
				Capability:  cpb.Capability_CAPABILITY_FILES.Enum(),
				Path: []*cpb.Function{
					&cpb.Function{Name: proto.String("(*p1.Embedder).M"), Package: proto.String("p1")},
					&cpb.Function{Name: proto.String("(p2.Foo).M"), Package: proto.String("p2")},
					&cpb.Function{Name: proto.String("p2.Interesting"), Package: proto.String("p2")},
				},
				PackageDir: proto.String("p1"),
			},
			{
				PackageName: proto.String("p1"),
				Capability:  cpb.Capability_CAPABILITY_FILES.Enum(),
				Path: []*cpb.Function{
					&cpb.Function{Name: proto.String("(*p1.Embedder).PM"), Package: proto.String("p1")},
					&cpb.Function{Name: proto.String("(*p2.Foo).PM"), Package: proto.String("p2")},
					&cpb.Function{Name: proto.String("p2.Interesting"), Package: proto.String("p2")},
				},
				PackageDir: proto.String("p1"),
			},
			{
				PackageName: proto.String("p2"),
				Capability:  cpb.Capability_CAPABILITY_FILES.Enum(),
				Path: []*cpb.Function{
					&cpb.Function{Name: proto.String("p2.Interesting"), Package: proto.String("p2")},
				},
				PackageDir: proto.String("p2"),
			},
			{
				PackageName: proto.String("p2"),
				Capability:  cpb.Capability_CAPABILITY_FILES.Enum(),
				Path: []*cpb.Function{
					&cpb.Function{Name: proto.String("(*p2.Foo).PM"), Package: proto.String("p2")},
					&cpb.Function{Name: proto.String("p2.Interesting"), Package: proto.String("p2")},
				},
				PackageDir: proto.String("p2"),
			},
			{
				PackageName: proto.String("p2"),
				Capability:  cpb.Capability_CAPABILITY_FILES.Enum(),
				Path: []*cpb.Function{
					&cpb.Function{Name: proto.String("(p2.Foo).M"), Package: proto.String("p2")},
					&cpb.Function{Name: proto.String("p2.Interesting"), Package: proto.String("p2")},
				},
				PackageDir: proto.String("p2"),
			},
			{
				PackageName: proto.String("p2"),
				Capability:  cpb.Capability_CAPABILITY_FILES.Enum(),
				Path: []*cpb.Function{
					&cpb.Function{Name: proto.String("(p2.Foo).M$bound"), Package: proto.String("p2")},
					&cpb.Function{Name: proto.String("(p2.Foo).M"), Package: proto.String("p2")},
					&cpb.Function{Name: proto.String("p2.Interesting"), Package: proto.String("p2")},
				},
				PackageDir: proto.String("p2"),
			},
			{
				PackageName: proto.String("p2"),
				Capability:  cpb.Capability_CAPABILITY_FILES.Enum(),
				Path: []*cpb.Function{
					&cpb.Function{Name: proto.String("(*p2.Foo).M$thunk"), Package: proto.String("p2")},
					&cpb.Function{Name: proto.String("(p2.Foo).M"), Package: proto.String("p2")},
					&cpb.Function{Name: proto.String("p2.Interesting"), Package: proto.String("p2")},
				},
				PackageDir: proto.String("p2"),
			},
			{
				PackageName: proto.String("p2"),
				Capability:  cpb.Capability_CAPABILITY_FILES.Enum(),
				Path: []*cpb.Function{
					&cpb.Function{Name: proto.String("(p2.Foo).M$thunk"), Package: proto.String("p2")},
					&cpb.Function{Name: proto.String("(p2.Foo).M"), Package: proto.String("p2")},
					&cpb.Function{Name: proto.String("p2.Interesting"), Package: proto.String("p2")},
				},
				PackageDir: proto.String("p2"),
			},
			{
				PackageName: proto.String("p2"),
				Capability:  cpb.Capability_CAPABILITY_FILES.Enum(),
				Path: []*cpb.Function{
					&cpb.Function{Name: proto.String("(*p2.Foo).M"), Package: proto.String("p2")},
					&cpb.Function{Name: proto.String("(p2.Foo).M"), Package: proto.String("p2")},
					&cpb.Function{Name: proto.String("p2.Interesting"), Package: proto.String("p2")},
				},
				PackageDir: proto.String("p2"),
			},
		},
	}

	got := GetCapabilityInfo(graph, config)
	opts := []cmp.Option{
		protocmp.Transform(),
		protocmp.SortRepeated(func(a, b *cpb.CapabilityInfo) bool {
			if u, v := a.GetCapability(), b.GetCapability(); u != v {
				return u < v
			}
			if c := strings.Compare(a.GetPackageDir(), b.GetPackageDir()); c != 0 {
				return c < 0
			}
			if len(a.Path) == 0 {
				return false
			}
			if len(b.Path) == 0 {
				return true
			}
			return a.Path[0].GetName() < b.Path[0].GetName()
		}),
		protocmp.IgnoreFields(&cpb.CapabilityInfoList{}, "package_info"),
		protocmp.IgnoreFields(&cpb.CapabilityInfo{}, "dep_path"),
		protocmp.IgnoreFields(&cpb.CapabilityInfo{}, "capability_type"),
		protocmp.IgnoreFields(&cpb.Function{}, "site"),
		protocmp.IgnoreFields(&cpb.Function_Site{}, "filename"),
		protocmp.IgnoreFields(&cpb.Function_Site{}, "line"),
		protocmp.IgnoreFields(&cpb.Function_Site{}, "column"),
	}
	if diff := cmp.Diff(expected, got, opts...); diff != "" {
		t.Errorf("GetCapabilityInfo: got %v, want %v; diff %s",
			got, expected, diff)
	}
}
