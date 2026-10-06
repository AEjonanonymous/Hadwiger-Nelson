import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

-- AUDIT SOLUTION (not part of the original repository).
-- The definitions below are copied character for character from `comparator/Challenge.lean`
-- (`Circle`, `is_unit_safe`, `SixColoring`, `angle_to_point`, `color_measure`, `SafeDensity`); the unused `θ` is left out.
-- `coloring_collision` is copied, statement and proof, from `comparator/Solution.lean`; the proof of A.1 uses it.
-- Everything after it is the audit's.

open Real InnerProductSpace MeasureTheory

-- 1.1 Define the Circle as a set of points at distance 'r' from origin
def Circle (r : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) := 
  {p | ‖p‖ = r}

-- 1.3 Define the Unit-Safe property
def is_unit_safe (S : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, dist u v ≠ 1

-- 2.1 A structure representing a hypothetical proper 6-coloring of the circle
structure SixColoring (r : ℝ) where
  color : Fin 6 → Set (EuclideanSpace ℝ (Fin 2))
  on_circle : ∀ i, color i ⊆ Circle r
  covering : (⋃ i, color i) = Circle r
  proper : ∀ i, is_unit_safe (color i)

-- 3.1 The Angle Map
noncomputable def angle_to_point (r : ℝ) (α : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  (WithLp.equiv 2 (Fin 2 → ℝ)).symm ![r * cos α, r * sin α]

-- 3.2 Define the length of a color's arc
noncomputable def color_measure (r : ℝ) (S : Set (EuclideanSpace ℝ (Fin 2))) : ℝ :=
  (volume (angle_to_point r ⁻¹' S ∩ Set.Ico 0 (2 * π))).toReal

-- 4.2 The density limit as a property of Unit-Safe sets
def SafeDensity (r : ℝ) (S : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  is_unit_safe S → color_measure r S < π / 3

-- 4.3 The Collision Theorem Proof (Proof by Exclusion)
theorem coloring_collision (r : ℝ) (C : SixColoring r) (h_safe : ∀ i, SafeDensity r (C.color i)) : 
  (∑ i, color_measure r (C.color i)) < 2 * π := by
  have h_each : ∀ i, color_measure r (C.color i) < π / 3 := fun i => h_safe i (C.proper i)
  calc
    (∑ i : Fin 6, color_measure r (C.color i)) 
      < ∑ i : Fin 6, π / 3 := Finset.sum_lt_sum (λ i _ => (h_each i).le) ⟨0, Finset.mem_univ _, h_each 0⟩
    _ = 6 * (π / 3)        := by simp
    _ = 2 * π              := by ring

-- A.0 Supporting facts: the angle map lands on the circle, and six sets covering the circle have total measure ≥ 2π
theorem norm_angle_to_point {r : ℝ} (hr : 0 ≤ r) (α : ℝ) : ‖angle_to_point r α‖ = r := by
  rw [EuclideanSpace.norm_eq]
  simp [angle_to_point, Fin.sum_univ_two, mul_pow]
  rw [← mul_add, cos_sq_add_sin_sq, mul_one, Real.sqrt_sq hr]

theorem two_pi_le_sum {r : ℝ} (hr : 0 ≤ r) (C : SixColoring r) :
    2 * π ≤ ∑ i, color_measure r (C.color i) := by
  set A : Fin 6 → Set ℝ := fun i => angle_to_point r ⁻¹' C.color i ∩ Set.Ico 0 (2 * π) with hA
  have hcov : Set.Ico 0 (2 * π) ⊆ ⋃ i, A i := by
    intro α hα
    have : angle_to_point r α ∈ Circle r := by simp [Circle, norm_angle_to_point hr]
    rw [← C.covering] at this
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp this
    exact Set.mem_iUnion.mpr ⟨i, hi, hα⟩
  have hfin : ∀ i, volume (A i) ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)
      (measure_mono Set.inter_subset_right)
  have h1 : volume (Set.Ico 0 (2 * π)) ≤ ∑ i, volume (A i) :=
    (measure_mono hcov).trans (measure_iUnion_fintype_le _ _)
  have h2 := ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr fun i _ => hfin i) h1
  rw [ENNReal.toReal_sum (fun i _ => hfin i), Real.volume_Ico,
    ENNReal.toReal_ofReal (by linarith [pi_pos])] at h2
  simpa [color_measure, A] using h2

theorem color_measure_circle {r : ℝ} (hr : 0 ≤ r) : color_measure r (Circle r) = 2 * π := by
  have hpre : angle_to_point r ⁻¹' Circle r = Set.univ := by
    ext α
    simp [Circle, norm_angle_to_point hr]
  rw [color_measure, hpre, Set.univ_inter, Real.volume_Ico, ENNReal.toReal_ofReal (by linarith [pi_pos])]
  ring

theorem circle_quarter_unit_safe : is_unit_safe (Circle (1 / 4)) := by
  intro u hu v hv h
  have hu' : ‖u‖ = 1 / 4 := hu
  have hv' : ‖v‖ = 1 / 4 := hv
  have := norm_sub_le u v
  rw [dist_eq_norm] at h
  linarith

-- A.1 The hypothesis of `coloring_collision` is met by no six-colouring of a circle of radius r ≥ 0.
-- If it were, `coloring_collision` would give a total below 2π, but the six classes cover the circle.
theorem hypothesis_never_holds (r : ℝ) (hr : 0 ≤ r) (C : SixColoring r) :
    ¬ ∀ i, SafeDensity r (C.color i) := fun h =>
  absurd (coloring_collision r C h) (not_lt.mpr (two_pi_le_sum hr C))

-- A.2 The assumed density bound fails for the whole circle of radius 1/4:
-- it has no two points at distance 1 (its diameter is 1/2), and its angular measure is 2π.
theorem density_bound_false_at_quarter : ¬ SafeDensity (1 / 4) (Circle (1 / 4)) := by
  intro h
  have := h circle_quarter_unit_safe
  rw [color_measure_circle (by norm_num)] at this
  linarith [pi_pos]
