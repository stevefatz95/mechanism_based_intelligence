# Mechanism-Based Intelligence (MBI)

This repository contains the code and supplementary materials for *Mechanism-Based Intelligence: Differentiable Incentives for Rational Coordination and Guaranteed Alignment in Multi-Agent Systems* (arXiv:2512.20688).

## Overview

MBI combines mechanism design, economic theory and differentiable computation to coordinate self-interested, computationally bounded agents. Its core component, the Differentiable Price Mechanism (DPM), computes each agent's price as the gradient of the system loss; subtracting its own marginal cost, each agent obtains an incentive signal that aligns its best response with the global objective. Under the conditions stated in the paper (a differentiable, jointly strictly convex global loss), the induced game is an exact potential game whose unique equilibrium is the global optimum.

## Contents

* `notebooks/mbi_appendix_c.ipynb`: the numerical experiments of Appendix C (Sections C.1 to C.12), with all outputs and figures.
* `lean/`: Lean 4 checks of the arguments of Theorems 1 to 4 (see below).
* `requirements.txt`: Python dependencies.

## Running the Notebook

Tested with Python 3.10.13, PyTorch 2.9.0 and NumPy 2.0.1 on a Mac M4.

```bash
git clone https://github.com/stevefatz95/mechanism_based_intelligence.git
cd mechanism_based_intelligence
pip install -r requirements.txt
jupyter notebook notebooks/mbi_appendix_c.ipynb
```

Run all cells from the top (Kernel → Restart & Run All). All random initializations are seeded, so every reported number is reproducible, except the wall-clock timings in Section C.11, which depend on the hardware. The figures are saved to the working directory when the notebook runs.

## Lean 4 Checks

The `lean/` folder contains Lean 4 files that check the arguments of Theorems 1 to 4 using Mathlib. They take as hypotheses the first-order characterization of differentiable convex functions, the descent inequality for functions with Lipschitz gradient, an error bound in place of compactness in the last step of Theorem 4, and the monotonicity of the marginal effort gain derived in Theorem 2.

To check them (requires [Lean 4](https://lean-lang.org/) via `elan`):

```bash
cd lean
lake exe cache get        # downloads precompiled Mathlib
lake env lean mbi/Theorems.lean
lake env lean mbi/Stage2.lean
lake env lean mbi/Stage3.lean
```

The check succeeds if Lean reports no errors; linter warnings, if any, do not affect the proofs.

## Versions

* **v2** (current): corrected and extended theory (Appendix B) and experiments (Appendix C); see the arXiv version history for details.
* **v1**: code for the first arXiv version, available under the tag [`v1.0`](https://github.com/stevefatz95/mechanism_based_intelligence/tree/v1.0).

## Citation

If you use this work, please cite:

```bibtex
@misc{grassi2025mbi,
  title         = {Mechanism-Based Intelligence (MBI): Differentiable Incentives for Rational Coordination and Guaranteed Alignment in Multi-Agent Systems},
  author        = {Grassi, Stefano},
  year          = {2025},
  eprint        = {2512.20688},
  archivePrefix = {arXiv},
  primaryClass  = {cs.GT},
  url           = {https://arxiv.org/abs/2512.20688}
}
```

Paper: [arXiv:2512.20688](https://arxiv.org/abs/2512.20688)
