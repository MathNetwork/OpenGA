import OpenGALib.Comparison.BishopGromov
import OpenGALib.Comparison.Util.SpaceForm

/-!
# OpenGA Comparison Geometry (Layer 3b)

Comparison theorems of Riemannian geometry: Bishop–Gromov volume comparison,
Toponogov triangle comparison, Rauch comparison, Cheeger–Gromoll splitting,
critical-point theory of distance functions. These theorems consume the
Layer 1 metric / length / measure infrastructure and the Layer 3a
Riemannian primitives (Levi-Civita, Ricci, Bochner stack) and produce the
quantitative comparisons that underpin the modern paradigm of geometric
analysis (Cheeger–Colding, Cheeger–Naber, Liokumovich–Lishak–Nabutovsky).

Ground-truth references for the layer: do Carmo, *Riemannian Geometry*,
Ch. 10; Petersen, *Riemannian Geometry*, Ch. 6 + Ch. 9; Cheeger–Ebin,
*Comparison Theorems in Riemannian Geometry*.

## Current content

* `Comparison/BishopGromov/` — Bishop–Gromov volume comparison theorem.
  Statement landed as the north-star target driving Stage II of Layer 1
  + Layer 3a + Layer 3b development.
-/
