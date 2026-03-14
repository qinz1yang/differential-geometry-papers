# Differential Geometry Papers in Lean 4

This repository utilizes the [Differential Geometry Library](https://github.com/qinz1yang/differential-geometry) to formalize papers in differential geometry.

Please navigate to individual folders to see the description and axioms injected.

## Formalized Papers

### - [Harnack Estimate for the Endangered Species Equation](https://github.com/qinz1yang/differential-geometry-papers/tree/main/CaoCerenziaKazaras2014) - Xiaodong Cao, Mark Cerenzia, Demetre Kazaras

### - [Differential Harnack Estimates for Time-Dependent Heat Equations with Potentials](https://github.com/qinz1yang/differential-geometry-papers/tree/main/CaoHamilton2008) - Xiaodong Cao, Richard S. Hamilton

## File Structure

To compile this project, you need to clone both this repository and the [differential-geometry](https://github.com/qinz1yang/differential-geometry) repository in the same directory. 
```text

├── differential_geometry/         
│   ├── lakefile.toml
│   └── DifferentialGeometry.lean
└── differential-geometry-papers/  
    ├── lakefile.toml              
    ├── lean-toolchain             
    ├── CaoCerenziaKazaras2014/
    │   └── CaoCerenziaKazaras2014.lean
    └── CaoHamilton2008/           
        └── CaoHamilton2008.lean

```

After that, navigate to `differential-geometry-papers` and run `lake build`.

```bash
git clone https://github.com/qinz1yang/differential-geometry
git clone https://github.com/qinz1yang/differential-geometry-papers

cd differential-geometry-papers
lake build
```
