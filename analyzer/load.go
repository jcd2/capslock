// Copyright 2023 Google LLC
//
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file or at
// https://developers.google.com/open-source/licenses/bsd

package analyzer

import (
	"os"
	"sync"

	cpb "github.com/google/capslock/proto"
	"golang.org/x/tools/go/packages"
)

var (
	standardLibraryPackagesOnce sync.Once
	standardLibraryPackagesMap  map[string]struct{}
)

// LoadConfig specifies the build tags, GOOS value, and GOARCH value to use
// when loading packages.  These will be used to determine when a file's build
// constraint is satisfied.  See
// https://pkg.go.dev/cmd/go#hdr-Build_constraints for more information.
type LoadConfig struct {
	BuildTags string
	GOOS      string
	GOARCH    string
}

// PackagesLoadModeNeeded is a packages.LoadMode that has all the bits set for
// the information that this package uses to perform its analysis.  Users
// should load packages for analysis using this LoadMode (or a superset.)
const PackagesLoadModeNeeded packages.LoadMode = packages.NeedName |
	packages.NeedFiles |
	packages.NeedCompiledGoFiles |
	packages.NeedImports |
	packages.NeedDeps |
	packages.NeedTypes |
	packages.NeedSyntax |
	packages.NeedTypesInfo |
	packages.NeedTypesSizes |
	packages.NeedModule

func LoadPackages(packageNames []string, lcfg LoadConfig) ([]*packages.Package, error) {
	cfg := &packages.Config{Mode: PackagesLoadModeNeeded}
	if lcfg.BuildTags != "" {
		cfg.BuildFlags = []string{"-tags=" + lcfg.BuildTags}
	}
	if lcfg.GOOS != "" || lcfg.GOARCH != "" {
		env := append([]string(nil), os.Environ()...) // go1.21 has slices.Clone for this
		if lcfg.GOOS != "" {
			env = append(env, "GOOS="+lcfg.GOOS)
		}
		if lcfg.GOARCH != "" {
			env = append(env, "GOARCH="+lcfg.GOARCH)
		}
		cfg.Env = env
	}
	return packages.Load(cfg, packageNames...)
}

func standardLibraryPackages() map[string]struct{} {
	standardLibraryPackagesOnce.Do(func() {
		pkgs, err := packages.Load(nil, "std")
		if err != nil {
			panic(err.Error())
		}
		standardLibraryPackagesMap = make(map[string]struct{})
		for _, p := range pkgs {
			standardLibraryPackagesMap[p.PkgPath] = struct{}{}
		}
	})
	return standardLibraryPackagesMap
}

func collectModuleInfo(graph *cpb.Graph) []*cpb.ModuleInfo {
	mi := make([]*cpb.ModuleInfo, len(graph.Modules))
	for i, m := range graph.Modules {
		mi[i] = &cpb.ModuleInfo{
			Path:    m.Name,
			Version: m.Version,
		}
	}
	return mi
}

func collectPackageInfo(graph *cpb.Graph) []*cpb.PackageInfo {
	pi := make([]*cpb.PackageInfo, len(graph.Packages))
	for i, p := range graph.Packages {
		pi[i] = &cpb.PackageInfo{Path: p.Path}
	}
	return pi
}
