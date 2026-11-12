import Mathlib

/-!
# MBI: Stage 3 formal checks

Theorem 3 Part 1, Theorem 4 Part 1 (gradients vanish; convergence under an error bound),
and Theorem 2 in continuous effort.
-/

open Finset BigOperators Filter Topology

namespace MBI3

/-! ## Theorem 3, Part 1 (Appendix B.5): the Planner's belief does not enter the game -/

/-- The transfer t_i = -L_System + h_i (B.1.1) is a function of actions only. Whatever belief
`b` the Planner holds about private costs, every agent's utility is the same function of the
action profile, so the induced game, its Nash equilibria and (by Theorem 1) the outcome X*
for the true costs are unaffected. -/
theorem belief_irrelevant {X β : Type*} (Lsys : X → ℝ) (h : X → ℝ) (C_true : X → ℝ)
    (transfer : β → X → ℝ) (htransfer : ∀ b x, transfer b x = -Lsys x + h x) (b₁ b₂ : β) :
    (fun x => transfer b₁ x - C_true x) = (fun x => transfer b₂ x - C_true x) := by
  funext x
  rw [htransfer, htransfer]

/-! ## Theorem 4, Part 1 (Appendix B.6): the gradient tends to zero -/

/-- Summing (B.16): if each step lowers the loss by at least c * s k with c > 0 and s k ≥ 0
(s k = squared gradient norm, c = η (1 - η L / 2)), and the loss is bounded below by m, then
the partial sums of s are bounded by (L 0 - m) / c. -/
theorem partial_sums_bounded (L s : ℕ → ℝ) (c m : ℝ) (hc : 0 < c)
    (hdec : ∀ k, L (k + 1) ≤ L k - c * s k) (hb : ∀ k, m ≤ L k) :
    ∀ K, ∑ k ∈ range K, s k ≤ (L 0 - m) / c := by
  have tele : ∀ K, L K ≤ L 0 - c * ∑ k ∈ range K, s k := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [sum_range_succ]
      have := hdec K
      nlinarith
  intro K
  rw [le_div_iff₀ hc]
  have h1 := tele K
  have h2 := hb K
  nlinarith

/-- Theorem 4, Part 1: the squared gradient norm tends to zero along the iteration. -/
theorem gradient_tends_to_zero (L s : ℕ → ℝ) (c m : ℝ) (hc : 0 < c) (hs : ∀ k, 0 ≤ s k)
    (hdec : ∀ k, L (k + 1) ≤ L k - c * s k) (hb : ∀ k, m ≤ L k) :
    Tendsto s atTop (𝓝 0) :=
  (summable_of_sum_range_le hs (partial_sums_bounded L s c m hc hdec hb)).tendsto_atTop_zero

/-- Theorem 4, Part 1, last step, under an error bound: if the squared distance to X* is at
most A times the squared gradient norm (true for every strongly convex quadratic loss in
Appendix C, with A = 1 / μ^2), the iterates converge to X*. -/
theorem iterates_converge (L s dist2 : ℕ → ℝ) (c m A : ℝ) (hc : 0 < c) (hs : ∀ k, 0 ≤ s k)
    (hdec : ∀ k, L (k + 1) ≤ L k - c * s k) (hb : ∀ k, m ≤ L k)
    (hd : ∀ k, 0 ≤ dist2 k) (herr : ∀ k, dist2 k ≤ A * s k) :
    Tendsto dist2 atTop (𝓝 0) := by
  have hs0 := gradient_tends_to_zero L s c m hc hs hdec hb
  have hA : Tendsto (fun k => A * s k) atTop (𝓝 0) := by
    simpa using hs0.const_mul A
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hA hd herr

/-! ## Theorem 2 (Appendix B.4), continuous effort -/

/-- (B.12)-(B.13): if U is differentiable, U' ≥ 0 on (0, T*), U'(T*) ≤ 0 and U' is
non-increasing from T* on (as Theorem 2 derives under gradient ascent and convex κ),
then T* maximizes U over all T ≥ 0. -/
theorem continuous_stopping (U : ℝ → ℝ) (hU : Differentiable ℝ U) (Tstar : ℝ) (h0 : 0 ≤ Tstar)
    (hpos : ∀ t, 0 < t → t < Tstar → 0 ≤ deriv U t)
    (hanti : AntitoneOn (deriv U) (Set.Ici Tstar)) (hstop : deriv U Tstar ≤ 0) :
    ∀ T, 0 ≤ T → U T ≤ U Tstar := by
  intro T hT
  rcases le_total T Tstar with h | h
  · have hm : MonotoneOn U (Set.Icc 0 Tstar) :=
      monotoneOn_of_deriv_nonneg (convex_Icc 0 Tstar) hU.continuous.continuousOn
        hU.differentiableOn (fun x hx => by
          rw [interior_Icc] at hx
          exact hpos x hx.1 hx.2)
    exact hm ⟨hT, h⟩ ⟨h0, le_rfl⟩ h
  · have ha : AntitoneOn U (Set.Ici Tstar) :=
      antitoneOn_of_deriv_nonpos (convex_Ici Tstar) hU.continuous.continuousOn
        hU.differentiableOn (fun x hx => by
          rw [interior_Ici] at hx
          exact le_trans (hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr (le_of_lt hx))
            (le_of_lt hx)) hstop)
    exact ha (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr h) h

end MBI3
