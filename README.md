# Differential Geometry Papers in Lean 4

This repository utilizes the [Differential Geometry Library](https://github.com/qinz1yang/differential-geometry) to formalize papers in differential geometry.

Please navigate to individual folders to see the description and axioms injected.

## Formalized Papers

### 1. [Differential Harnack Estimates for Time-Dependent Heat Equations with Potentials](https://arxiv.org/abs/0807.0568) - Xiaodong Cao, Richard S. Hamilton

## File Structure

To compile this project, you need to clone both this repository and the differential-geometry repository in the same directory. 
```text
.
├── differential-geometry/
│   ├── lakefile.toml
│   └── DifferentialGeometry.lean
└── differential-geometry-papers/
    ├── README.md
    ├── .gitignore
    └── CaoHamilton2008/
        ├── README.md
        ├── lakefile.toml
        └── CaoHamilton2008.lean
```

After that, navigate to individual folders for papers and run `lake build`. For example, for CaoHamilton2008, run the following commands:

```bash
git clone https://github.com/qinz1yang/differential-geometry
git clone https://github.com/qinz1yang/differential-geometry-papers
cd differential-geometry-papers/CaoHamilton2008
lake build CaoHamilton2008
```
