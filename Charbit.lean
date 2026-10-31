import Mathlib

open scoped ENNReal NNReal

namespace Charbit

/-- Six classes of two vertices each. -/
abbrev Vertex := Fin 12

/-- Forward arcs inside each class, and all arcs to the next class. -/
def Arc (u v : Vertex) : Prop :=
  (u.val / 2 = v.val / 2 ∧ u.val % 2 < v.val % 2) ∨
  ((u.val / 2 + 1) % 6 = v.val / 2)

instance : DecidableRel Arc := fun u v => by
  unfold Arc
  infer_instance

/-- No vertex has an arc to itself. -/
theorem loopless : ∀ u : Vertex, ¬ Arc u u := by
  decide

/-- Opposite arcs never occur. -/
theorem oriented :
    ∀ u v : Vertex, Arc u v → ¬ Arc v u := by
  decide

/-- The graph contains the displayed directed six-cycle. -/
theorem displayed_six_cycle :
    Arc 0 2 ∧ Arc 2 4 ∧ Arc 4 6 ∧
    Arc 6 8 ∧ Arc 8 10 ∧ Arc 10 0 := by
  decide

end Charbit

namespace Charbit

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- A directed walk of exactly k steps. -/
def Walk : Nat → Vertex → Vertex → Prop
  | 0, u, v => u = v
  | k + 1, u, v => ∃ w : Vertex, Arc u w ∧ Walk k w v

instance walkDecidable (k : Nat) (u v : Vertex) :
    Decidable (Walk k u v) := by
  induction k generalizing u v with
  | zero =>
      change Decidable (u = v)
      infer_instance
  | succ k ih =>
      change Decidable (∃ w : Vertex, Arc u w ∧ Walk k w v)
      letI : DecidableRel (Walk k) := fun a b => ih a b
      infer_instance

theorem no_short_closed_walk :
    ∀ k : Fin 5, ∀ u : Vertex,
      ¬ Walk (k.val + 1) u u := by
  decide

end Charbit

namespace Charbit

/-- The real adjacency matrix of our graph. -/
def adjacency : Matrix Vertex Vertex ℝ :=
  fun u v => if Arc u v then 1 else 0

/-- Coordinates (sqrt 2, 1), repeated in all six classes. -/
noncomputable def eigenvector : Vertex → ℝ :=
  fun u => if u.val % 2 = 0 then Real.sqrt 2 else 1

/-- The explicit eigenvector identity. -/
theorem eigenpair :
    adjacency.mulVec eigenvector =
      (1 + Real.sqrt 2) • eigenvector := by
  ext u
  fin_cases u <;>
    norm_num [adjacency, eigenvector, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, Arc] <;>
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

end Charbit

namespace Charbit

def complexAdjacency : Matrix Vertex Vertex ℂ :=
  fun u v => (adjacency u v : ℂ)

noncomputable def complexEigenvector : Vertex → ℂ :=
  fun u => (eigenvector u : ℂ)

theorem complex_eigenpair :
    complexAdjacency.mulVec complexEigenvector =
      (1 + (Real.sqrt 2 : ℂ)) • complexEigenvector := by
  ext u
  have h := congrArg (fun r : ℝ => (r : ℂ))
    (congrFun eigenpair u)
  simpa [complexAdjacency, complexEigenvector,
    Matrix.mulVec, dotProduct] using h

theorem complex_eigenvector_ne_zero :
    complexEigenvector ≠ 0 := by
  intro h
  have h1 := congrFun h (1 : Vertex)
  norm_num [complexEigenvector, eigenvector] at h1

theorem eigenvalue_mem_spectrum :
    (1 + (Real.sqrt 2 : ℂ)) ∈
      spectrum ℂ complexAdjacency := by
  rw [← Matrix.spectrum_toLin']
  apply Module.End.HasEigenvalue.mem_spectrum
  apply Module.End.hasEigenvalue_of_hasEigenvector
    (x := complexEigenvector)
  refine ⟨Module.End.mem_eigenspace_iff.mpr ?_,
    complex_eigenvector_ne_zero⟩
  simpa using complex_eigenpair

end Charbit

namespace Charbit

theorem eigenvalue_gt_threshold :
    (12 / 5 : ℝ) < 1 + Real.sqrt 2 := by
  have hs := Real.sqrt_nonneg (2 : ℝ)
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith

theorem spectral_radius_gt :
    (12 / 5 : ℝ≥0∞) < spectralRadius ℂ complexAdjacency := by
  have hnorm :
      ‖(1 + (Real.sqrt 2 : ℂ))‖ = 1 + Real.sqrt 2 := by
    have hc :
        (1 + (Real.sqrt 2 : ℂ)) =
          ((1 + Real.sqrt 2 : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [hc, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  have hnn :
      (12 / 5 : ℝ≥0) < ‖(1 + (Real.sqrt 2 : ℂ))‖₊ := by
    change (12 / 5 : ℝ) < ‖(1 + (Real.sqrt 2 : ℂ))‖
    rw [hnorm]
    exact eigenvalue_gt_threshold
  have hsmall :
      (12 / 5 : ℝ≥0∞) <
        (‖(1 + (Real.sqrt 2 : ℂ))‖₊ : ℝ≥0∞) := by
    have hcast := ENNReal.coe_lt_coe.mpr hnn
    norm_num at hcast ⊢
    exact hcast
  have hbound :
      (‖(1 + (Real.sqrt 2 : ℂ))‖₊ : ℝ≥0∞) ≤
        spectralRadius ℂ complexAdjacency := by
    unfold spectralRadius
    apply le_iSup_of_le (1 + (Real.sqrt 2 : ℂ))
    apply le_iSup_of_le eigenvalue_mem_spectrum
    exact le_rfl
  exact lt_of_lt_of_le hsmall hbound

/-- The twelve-vertex counterexample at threshold parameter k = 5. -/
theorem counterexample :
    (∀ u : Vertex, ¬ Arc u u) ∧
    (∀ u v : Vertex, Arc u v → ¬ Arc v u) ∧
    (∀ k : Fin 5, ∀ u : Vertex,
      ¬ Walk (k.val + 1) u u) ∧
    (12 / 5 : ℝ≥0∞) < spectralRadius ℂ complexAdjacency := by
  exact ⟨loopless, oriented, no_short_closed_walk,
    spectral_radius_gt⟩

end Charbit
