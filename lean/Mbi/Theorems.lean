import Mathlib

open Finset BigOperators

namespace MBI

/-! ## Theorem 1 (Appendix B.3): Groves-form transfer and exact potential game -/

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]

/-- Global loss (B.3): system loss plus all private costs. -/
def Lglob (Lsys : (ι → E) → ℝ) (C : ι → E → ℝ) (x : ι → E) : ℝ :=
  Lsys x + ∑ j, C j (x j)

/-- Agent utility (B.4): transfer t_i = -L_System + h_i, minus own cost. -/
def U (Lsys : (ι → E) → ℝ) (C : ι → E → ℝ) (h : ι → (ι → E) → ℝ)
    (i : ι) (x : ι → E) : ℝ :=
  (-Lsys x + h i x) - C i (x i)

/-- (B.8): the utility equals -L_global plus terms that do not involve agent i's own cost. -/
theorem U_eq (Lsys : (ι → E) → ℝ) (C : ι → E → ℝ) (h : ι → (ι → E) → ℝ)
    (i : ι) (x : ι → E) :
    U Lsys C h i x = -Lglob Lsys C x + (h i x + ∑ j ∈ univ.erase i, C j (x j)) := by
  have key : ∑ j, C j (x j) = C i (x i) + ∑ j ∈ univ.erase i, C j (x j) :=
    (add_sum_erase univ (fun j => C j (x j)) (mem_univ i)).symm
  unfold U Lglob
  rw [key]
  ring

/-- The other agents' costs do not depend on agent i's action. -/
theorem rest_indep (C : ι → E → ℝ) (i : ι) (x y : ι → E)
    (hxy : ∀ j, j ≠ i → x j = y j) :
    ∑ j ∈ univ.erase i, C j (x j) = ∑ j ∈ univ.erase i, C j (y j) := by
  apply sum_congr rfl
  intro j hj
  rw [hxy j (ne_of_mem_erase hj)]

/-- (B.8)-(B.9): exact potential property. For a unilateral deviation of agent i
(x and y agree except at i), and h_i independent of agent i's action, the change in
U_i equals minus the change in L_global. -/
theorem exact_potential (Lsys : (ι → E) → ℝ) (C : ι → E → ℝ) (h : ι → (ι → E) → ℝ)
    (i : ι) (x y : ι → E) (hxy : ∀ j, j ≠ i → x j = y j) (hh : h i x = h i y) :
    U Lsys C h i y - U Lsys C h i x = -(Lglob Lsys C y - Lglob Lsys C x) := by
  rw [U_eq, U_eq, hh, rest_indep C i x y hxy]
  ring

/-- (B.9): a deviation is weakly worse for agent i iff it weakly raises L_global. -/
theorem br_iff (Lsys : (ι → E) → ℝ) (C : ι → E → ℝ) (h : ι → (ι → E) → ℝ)
    (i : ι) (x y : ι → E) (hxy : ∀ j, j ≠ i → x j = y j) (hh : h i x = h i y) :
    U Lsys C h i y ≤ U Lsys C h i x ↔ Lglob Lsys C x ≤ Lglob Lsys C y := by
  have := exact_potential Lsys C h i x y hxy hh
  constructor <;> intro H <;> linarith

/-- Theorem 1 (one direction): a global minimizer of L_global is a Nash equilibrium of the
game induced by the DPM transfers. `hdep` states that h_i depends only on X_{-i}. -/
theorem optimum_is_NE (Lsys : (ι → E) → ℝ) (C : ι → E → ℝ) (h : ι → (ι → E) → ℝ)
    (hdep : ∀ i (x y : ι → E), (∀ j, j ≠ i → x j = y j) → h i x = h i y)
    (xstar : ι → E) (hmin : ∀ y, Lglob Lsys C xstar ≤ Lglob Lsys C y) :
    ∀ i (y : ι → E), (∀ j, j ≠ i → xstar j = y j) → U Lsys C h i y ≤ U Lsys C h i xstar := by
  intro i y hxy
  exact (br_iff Lsys C h i xstar y hxy (hdep i xstar y hxy)).mpr (hmin y)

/-! ## Theorem 3, Part 2 (Appendix B.5): certainty equivalence -/

/-- (B.15) for a prior with finite support: if the loss is affine in the cost parameter,
L(x; v) = A + v * B, its expectation equals its value at the mean parameter. -/
theorem certainty_equivalence {n : ℕ} (p v : Fin n → ℝ) (hp : ∑ k, p k = 1) (A B : ℝ) :
    ∑ k, p k * (A + v k * B) = A + (∑ k, p k * v k) * B := by
  have h1 : ∑ k, p k * (A + v k * B) = (∑ k, p k) * A + (∑ k, p k * v k) * B := by
    rw [sum_mul, sum_mul, ← sum_add_distrib]
    apply sum_congr rfl
    intro k _
    ring
  rw [h1, hp]
  ring

/-- Theorem 3, Part 2: a minimizer of the loss priced at the mean parameter minimizes the
expected loss. -/
theorem ce_argmin {X : Type*} {n : ℕ} (p v : Fin n → ℝ) (hp : ∑ k, p k = 1)
    (A B : X → ℝ) (xbar : X)
    (hmin : ∀ x, A xbar + (∑ k, p k * v k) * B xbar ≤ A x + (∑ k, p k * v k) * B x) :
    ∀ x, ∑ k, p k * (A xbar + v k * B xbar) ≤ ∑ k, p k * (A x + v k * B x) := by
  intro x
  rw [certainty_equivalence p v hp, certainty_equivalence p v hp]
  exact hmin x

/-! ## Theorem 2 (Appendix B.4), discrete form: optimal stopping -/

/-- If the gain of step t is non-increasing in t and each step costs c, stopping at the first
step T with gain ≤ c maximizes the total net gain ∑_{t<S} (g t - c) over all S. -/
theorem first_crossing_optimal (g : ℕ → ℝ) (c : ℝ) (hg : Antitone g) (T : ℕ)
    (hT : ∀ t < T, c < g t) (hTc : g T ≤ c) :
    ∀ S, ∑ t ∈ range S, (g t - c) ≤ ∑ t ∈ range T, (g t - c) := by
  intro S
  rcases le_total S T with hST | hTS
  · rw [← sum_range_add_sum_Ico _ hST]
    have : 0 ≤ ∑ t ∈ Ico S T, (g t - c) := sum_nonneg (fun t ht => by
      have := hT t (mem_Ico.mp ht).2
      linarith)
    linarith
  · rw [← sum_range_add_sum_Ico _ hTS]
    have : ∑ t ∈ Ico T S, (g t - c) ≤ 0 := sum_nonpos (fun t ht => by
      have := hg (mem_Ico.mp ht).1
      linarith)
    linarith

/-! ## Theorem 4, Part 2 (Appendix B.6): finitely many updating rounds -/

/-- If every one of the first K rounds lowers the loss by at least δ > 0 (what (B.16) gives
for an updating round) and the loss is bounded below by m, then K * δ ≤ L 0 - m. -/
theorem update_bound (L : ℕ → ℝ) (m δ : ℝ) (hbound : ∀ k, m ≤ L k) (K : ℕ)
    (hdec : ∀ k < K, L (k + 1) ≤ L k - δ) : (K : ℝ) * δ ≤ L 0 - m := by
  have key : ∀ k, k ≤ K → L k ≤ L 0 - k * δ := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have h1 := ih (Nat.le_of_succ_le hk)
      have h2 := hdec k (Nat.lt_of_succ_le hk)
      push_cast
      linarith
  have h3 := key K le_rfl
  have h4 := hbound K
  linarith

end MBI
