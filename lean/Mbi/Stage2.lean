import Mathlib

open Finset BigOperators

namespace MBI2

variable {n : ℕ}

/-! ## Theorem 1 (Appendix B.3): every Nash equilibrium is the unique global optimum -/

/-- A Nash equilibrium of the DPM game is a profile at which no unilateral change of any
coordinate lowers L_global (Theorem 1: each agent's utility is -L_global plus terms that do
not depend on its own action). With an interior optimum (B.1.1) and a gradient `g` along
every line (C^1, Assumption 1), all partial derivatives vanish at such a profile. -/
theorem gradient_zero_of_NE (f : (Fin n → ℝ) → ℝ) (x g : Fin n → ℝ)
    (hD : ∀ v : Fin n → ℝ, HasDerivAt (fun t : ℝ => f (x + t • v)) (∑ i, g i * v i) 0)
    (hNE : ∀ (i : Fin n) (s : ℝ), f x ≤ f (x + s • Pi.single i (1 : ℝ))) :
    ∀ i, g i = 0 := by
  intro i
  have hmin : IsLocalMin (fun t : ℝ => f (x + t • Pi.single i (1 : ℝ))) 0 :=
    Filter.Eventually.of_forall (fun s => by simpa using hNE i s)
  have h0 := hmin.hasDerivAt_eq_zero (hD (Pi.single i 1))
  simpa [Pi.single_apply] using h0

/-- Theorem 1: with the gradient inequality of a differentiable convex function,
a Nash equilibrium is a global minimizer of L_global. -/
theorem NE_is_global_min (f : (Fin n → ℝ) → ℝ) (x g : Fin n → ℝ)
    (hD : ∀ v : Fin n → ℝ, HasDerivAt (fun t : ℝ => f (x + t • v)) (∑ i, g i * v i) 0)
    (hNE : ∀ (i : Fin n) (s : ℝ), f x ≤ f (x + s • Pi.single i (1 : ℝ)))
    (hgrad : ∀ y : Fin n → ℝ, f x + ∑ i, g i * (y i - x i) ≤ f y) :
    ∀ y, f x ≤ f y := by
  intro y
  have hg := gradient_zero_of_NE f x g hD hNE
  have := hgrad y
  simpa [hg] using this

/-- Assumption 1: under strict convexity, the global minimizer is unique. -/
theorem global_min_unique (f : (Fin n → ℝ) → ℝ) (hf : StrictConvexOn ℝ Set.univ f)
    (x y : Fin n → ℝ) (hx : ∀ z, f x ≤ f z) (hy : ∀ z, f y ≤ f z) : x = y := by
  by_contra hne
  have hmid := hf.2 (Set.mem_univ x) (Set.mem_univ y) hne
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hmid
  have h1 := hx ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y)
  have h2 := hy x
  have h3 := hx y
  linarith

/-- Theorem 1: the Nash equilibrium coincides with the unique global optimum X*. -/
theorem NE_eq_optimum (f : (Fin n → ℝ) → ℝ) (hf : StrictConvexOn ℝ Set.univ f)
    (x g xstar : Fin n → ℝ)
    (hD : ∀ v : Fin n → ℝ, HasDerivAt (fun t : ℝ => f (x + t • v)) (∑ i, g i * v i) 0)
    (hNE : ∀ (i : Fin n) (s : ℝ), f x ≤ f (x + s • Pi.single i (1 : ℝ)))
    (hgrad : ∀ y : Fin n → ℝ, f x + ∑ i, g i * (y i - x i) ≤ f y)
    (hstar : ∀ z, f xstar ≤ f z) : x = xstar :=
  global_min_unique f hf x xstar (NE_is_global_min f x g hD hNE hgrad) hstar

/-! ## Theorem 4 (Appendix B.6): decrease per updating round -/

/-- (B.16). Updating agents step along their incentive, the others satisfice: the step is
-η d with d i = g i for updating coordinates and d i = 0 otherwise (g is the gradient of
L_global, so -g is the incentive G). Given the descent inequality of a function with
L-Lipschitz gradient, the loss falls by η (1 - η L / 2) times the squared step size. -/
theorem descent_step (f : (Fin n → ℝ) → ℝ) (L η : ℝ) (x g d : Fin n → ℝ)
    (hd : ∀ i, d i = 0 ∨ d i = g i)
    (hsmooth : f (x - η • d) ≤ f x - η * ∑ i, g i * d i + L / 2 * η ^ 2 * ∑ i, d i ^ 2) :
    f (x - η • d) ≤ f x - η * (1 - η * L / 2) * ∑ i, d i ^ 2 := by
  have hsum : ∑ i, g i * d i = ∑ i, d i ^ 2 := by
    apply sum_congr rfl
    intro i _
    rcases hd i with h | h <;> rw [h] <;> ring
  rw [hsum] at hsmooth
  calc f (x - η • d) ≤ f x - η * ∑ i, d i ^ 2 + L / 2 * η ^ 2 * ∑ i, d i ^ 2 := hsmooth
    _ = f x - η * (1 - η * L / 2) * ∑ i, d i ^ 2 := by ring

/-- Theorem 4, Part 2: if at least one agent updates, the satisficing check (B.13) gives
η * ∑ d i ^ 2 > ∂κ/∂T; with 0 < η < 2/L the round lowers L_global by more than
(1 - η L / 2) ∂κ/∂T. Together with `MBI.update_bound` (Stage 1) this bounds the number of
updating rounds. -/
theorem round_decrease (f : (Fin n → ℝ) → ℝ) (L η κ' : ℝ) (x g d : Fin n → ℝ)
    (hd : ∀ i, d i = 0 ∨ d i = g i)
    (hsmooth : f (x - η • d) ≤ f x - η * ∑ i, g i * d i + L / 2 * η ^ 2 * ∑ i, d i ^ 2)
    (hstep : η * L < 2) (hcheck : κ' < η * ∑ i, d i ^ 2) :
    f (x - η • d) < f x - (1 - η * L / 2) * κ' := by
  have h1 := descent_step f L η x g d hd hsmooth
  have hfac : 0 < 1 - η * L / 2 := by linarith
  have h2 : (1 - η * L / 2) * κ' < (1 - η * L / 2) * (η * ∑ i, d i ^ 2) :=
    mul_lt_mul_of_pos_left hcheck hfac
  nlinarith [h1, h2]

end MBI2
