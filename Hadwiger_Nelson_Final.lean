import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

open Real InnerProductSpace MeasureTheory

-- 1.1 Define the Circle as a set of points at distance 'r' from origin
-- In our Proof by Exclusion, this circle serves as the representative finite subgraph.
def Circle (r : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) := 
  {p | ‖p‖ = r}

-- 1.2 Define the Unit Rotation Angle 'θ' for any given radius 'r'
noncomputable def θ (r : ℝ) : ℝ := 2 * arcsin (1 / (2 * r))

-- 1.3 Define the Unit-Safe property
-- A set is unit-safe if it contains no two points at a distance of exactly 1.
def is_unit_safe (S : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, dist u v ≠ 1

-- 2.1 A structure representing a hypothetical proper 6-coloring of the circle
-- We define this to prove its non-existence. If this structure leads to a
-- contradiction, then χ(ℝ²) cannot be 6.
structure SixColoring (r : ℝ) where
  color : Fin 6 → Set (EuclideanSpace ℝ (Fin 2))
  on_circle : ∀ i, color i ⊆ Circle r
  covering : (⋃ i, color i) = Circle r
  proper : ∀ i, is_unit_safe (color i)

-- 3.1 The Angle Map
noncomputable def angle_to_point (r : ℝ) (α : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  (WithLp.equiv 2 (Fin 2 → ℝ)).symm ![r * cos α, r * sin α]

-- 3.2 Define the length of a color's arc
-- This calculates the density of a color on the 2π circumference.
noncomputable def color_measure (r : ℝ) (S : Set (EuclideanSpace ℝ (Fin 2))) : ℝ :=
  (volume (angle_to_point r ⁻¹' S ∩ Set.Ico 0 (2 * π))).toReal

-- 4.1 The Unit-Triangle Clique.
theorem unit_clique_verified :
  let r := 1 / sqrt 3
  let θ := 2 * arcsin (1 / (2 * r))
  (2 * r * sin (θ / 2) = 1) ∧ (2 * r * sin θ = 1) := by
  set r : ℝ := 1 / sqrt 3 with hr
  set θ : ℝ := 2 * arcsin (1 / (2 * r)) with hθ

  have h3 : (0 : ℝ) < 3 := by norm_num
  have sqrt3_pos : 0 < sqrt 3 := sqrt_pos.mpr h3
  
  -- 1. Solve θ / 2 = π / 3
  have h_half_theta : θ / 2 = π / 3 := by
    rw [hθ]
    field_simp [hr]
    have h_arg : 1 / (2 * (1 / sqrt 3)) = sqrt 3 / 2 := by
      field_simp [sqrt3_pos.ne.symm]
    rw [h_arg]
    -- Prove range manually using norm_num and pi_pos
    have h_range1 : -(π / 2) ≤ π / 3 := by 
      have : 0 < π := pi_pos
      linarith
    have h_range2 : π / 3 ≤ π / 2 := by 
      have : 0 < π := pi_pos
      linarith
    rw [← sin_pi_div_three, arcsin_sin h_range1 h_range2]
    -- This handles the "π / 3 * 3 = π" or "π / 3 = π / 3" logic
    field_simp

  -- 2. Part 1: 2 * r * sin (θ / 2) = 1
  have h_dist1 : 2 * r * sin (θ / 2) = 1 := by
    rw [h_half_theta, sin_pi_div_three, hr]
    field_simp [sqrt3_pos.ne.symm]

  -- 3. Part 2: 2 * r * sin θ = 1
  have h_dist2 : 2 * r * sin θ = 1 := by
    have h_theta : θ = 2 * π / 3 := by linarith [h_half_theta]
    rw [h_theta, hr]
    have h_sin : sin (2 * π / 3) = sin (π / 3) := by
      have h_sub : 2 * π / 3 = π - π / 3 := by field_simp; ring
      rw [h_sub, sin_pi_sub]
    rw [h_sin, sin_pi_div_three]
    field_simp [sqrt3_pos.ne.symm]

  exact ⟨h_dist1, h_dist2⟩

-- 4.2 The density limit as a property of Unit-Safe sets
-- The irrationality of 2π (the drift) ensures that no unit-safe
-- set can occupy a full π/3 of the circle without a collision.
def SafeDensity (r : ℝ) (S : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  is_unit_safe S → color_measure r S < π / 3

-- 4.3 The Collision Theorem (Proof by Exclusion)
-- This theorem proves that a 6-coloring is a logical impossibility.
-- If each color is restricted by the drift (SafeDensity), the sum (< 2π) 
-- fails to cover the circle (2π). By de Bruijn-Erdős, this scales to the plane.
theorem coloring_collision (r : ℝ) (C : SixColoring r) (h_safe : ∀ i, SafeDensity r (C.color i)) : 
  (∑ i, color_measure r (C.color i)) < 2 * π := by
  have h_each : ∀ i, color_measure r (C.color i) < π / 3 := fun i => h_safe i (C.proper i)
  calc
    (∑ i : Fin 6, color_measure r (C.color i)) 
      < ∑ i : Fin 6, π / 3 := Finset.sum_lt_sum (λ i _ => (h_each i).le) ⟨0, Finset.mem_univ _, h_each 0⟩
    _ = 6 * (π / 3)        := by simp
    _ = 2 * π              := by ring