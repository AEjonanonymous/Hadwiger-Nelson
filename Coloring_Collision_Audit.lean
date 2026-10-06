import Hadwiger_Nelson_Final

/-!
# An audit of `coloring_collision`

This file imports `Hadwiger_Nelson_Final` **unchanged** and proves four facts about its headline theorem

    theorem coloring_collision (r : ℝ) (C : SixColoring r) (h_safe : ∀ i, SafeDensity r (C.color i)) :
      (∑ i, color_measure r (C.color i)) < 2 * π

In words: *if* each of six colour classes covering the circle of radius `r` has angular measure below `π/3`
(that is the hypothesis `h_safe`; `SafeDensity r S` says "if `S` has no two points at distance 1, then its angular
measure is below `π/3`"), *then* the six measures add up to less than `2π`.

The results, strongest first. Each is proved below with no `sorry` and no axiom beyond Lean's standard three
(`propext`, `Classical.choice`, `Quot.sound`); the last lines of the file print the axioms of each.

* **(a) The theorem applies to nothing.** `Audit.hypothesis_never_holds`: for every radius `r ≥ 0` and every
  six-colouring `C` of that circle, the hypothesis `h_safe` is false. Equivalently
  (`Audit.some_class_breaks_the_bound`): every six-colouring of every circle has a colour class with no two points at
  distance 1 whose angular measure is at least `π/3`.
* **(b) The assumed bound is false.** `Audit.density_bound_false_at_quarter`: on the circle of radius `1/4` the whole
  circle has no two points at distance 1, and its angular measure is `2π`.
  `Audit.density_bound_false_at_inv_sqrt_three`: on the circle of radius `1/√3`, the arc of 120° has no two points at
  distance 1, and its angular measure is at least `2π/3`.
* **(c) The theorem uses no geometry.** `Audit.headline_from_six_numbers`: it follows in one line from the fact that
  six real numbers, each below `π/3`, add up to less than `2π` (`Audit.six_numbers`).
* **(d) Three colours suffice on the circle of radius `1/√3`.** `Audit.threeArcs`: three arcs of 120° are a proper
  colouring of that circle, in this repository's own structure `SixColoring`, with colours 3, 4 and 5 unused
  (`Audit.threeArcs_three_colours`).

**Remark, for completeness (negative radius).** For `r < 0` the set `Circle r` is empty, six empty classes form a
`SixColoring r`, and that colouring does satisfy `h_safe` (`Audit.emptyColouring_meets_hypothesis`). By (a) it is the only
situation in which the hypothesis holds: nothing is coloured, and the conclusion reads `0 < 2π`.

Nothing in `Hadwiger_Nelson_Final` mentions the plane, a graph or a chromatic number, so none of this file's
statements does either: they are about the circle, where that file's theorem lives.
-/

set_option autoImplicit false

open Real MeasureTheory

namespace Audit

/-! ## Two supporting facts -/

/-- The point at angle `α` on the circle of radius `r ≥ 0` has norm `r`: the angle map lands on the circle. -/
theorem norm_angle_to_point {r : ℝ} (hr : 0 ≤ r) (α : ℝ) : ‖angle_to_point r α‖ = r := by
  rw [EuclideanSpace.norm_eq]
  simp [angle_to_point, Fin.sum_univ_two, mul_pow]
  rw [← mul_add, cos_sq_add_sin_sq, mul_one, Real.sqrt_sq hr]

/-- **Covering costs `2π`.** Six sets that together cover the circle of radius `r ≥ 0` have angular measures adding
up to at least `2π`. (No measurability is assumed: this is countable subadditivity of Lebesgue outer measure.) -/
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

/-! ## (a) The theorem applies to nothing -/

/-- **(a)** For every radius `r ≥ 0` and every six-colouring `C` of the circle of radius `r`, the hypothesis of
`coloring_collision` is false.

The proof uses the repository's own theorem. If the hypothesis held, `coloring_collision` would give a total angular
measure below `2π`; but the six classes cover the circle, so their total is at least `2π` (`two_pi_le_sum`).
So there is no circle and no colouring to which `coloring_collision` can be applied. -/
theorem hypothesis_never_holds {r : ℝ} (hr : 0 ≤ r) (C : SixColoring r) :
    ¬ ∀ i, SafeDensity r (C.color i) := fun h =>
  absurd (coloring_collision r C h) (not_lt.mpr (two_pi_le_sum hr C))

/-- **(a), read as a statement about the bound.** Every six-colouring of every circle of radius `r ≥ 0` has a colour
class that contains no two points at distance 1 and has angular measure at least `π/3`. Each such class is a
counterexample to the density bound that `coloring_collision` assumes. -/
theorem some_class_breaks_the_bound {r : ℝ} (hr : 0 ≤ r) (C : SixColoring r) :
    ∃ i, is_unit_safe (C.color i) ∧ π / 3 ≤ color_measure r (C.color i) := by
  by_contra hne
  apply hypothesis_never_holds hr C
  intro i hsafe
  by_contra hlt
  exact hne ⟨i, hsafe, not_lt.mp hlt⟩

/-! ## (b) The assumed bound is false -/

/-- The whole circle of radius `r ≥ 0` has angular measure `2π`. -/
theorem color_measure_circle {r : ℝ} (hr : 0 ≤ r) : color_measure r (Circle r) = 2 * π := by
  have hpre : angle_to_point r ⁻¹' Circle r = Set.univ := by
    ext α
    simp [Circle, norm_angle_to_point hr]
  rw [color_measure, hpre, Set.univ_inter, Real.volume_Ico, ENNReal.toReal_ofReal (by linarith [pi_pos])]
  ring

/-- The circle of radius `1/4` contains no two points at distance 1: its diameter is `1/2`. -/
theorem circle_quarter_unit_safe : is_unit_safe (Circle (1 / 4)) := by
  intro u hu v hv h
  have hu' : ‖u‖ = 1 / 4 := hu
  have hv' : ‖v‖ = 1 / 4 := hv
  have := norm_sub_le u v
  rw [dist_eq_norm] at h
  linarith

/-- **(b), radius `1/4`.** The density bound fails for the whole circle of radius `1/4`: it has no two points at
distance 1, and its angular measure is `2π`, which is not below `π/3`. -/
theorem density_bound_false_at_quarter : ¬ SafeDensity (1 / 4) (Circle (1 / 4)) := by
  intro h
  have := h circle_quarter_unit_safe
  rw [color_measure_circle (by norm_num)] at this
  linarith [pi_pos]

/-- The squared distance between the points at angles `α` and `β` on the circle of radius `r` is
`2r²(1 − cos(α − β))` (the chord formula). -/
theorem dist_angle_to_point_sq (r α β : ℝ) :
    dist (angle_to_point r α) (angle_to_point r β) ^ 2 = 2 * r ^ 2 * (1 - cos (α - β)) := by
  rw [EuclideanSpace.dist_eq, sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  simp [angle_to_point, Fin.sum_univ_two, cos_sub, Real.dist_eq, sq_abs]
  linear_combination (r ^ 2) * (sin_sq_add_cos_sq α) + (r ^ 2) * (sin_sq_add_cos_sq β)

theorem cos_two_pi_div_three : cos (2 * π / 3) = -(1 / 2) := by
  have : 2 * π / 3 = π - π / 3 := by ring
  rw [this, cos_pi_sub, cos_pi_div_three]

/-- On the circle of radius `1/√3`, two points whose angles differ by less than `2π/3` (120°) are not at distance 1.
(There the points at distance exactly 1 are those exactly 120° apart: the paper's inscribed unit triangle.) -/
theorem dist_ne_one_of_abs_sub_lt {α β : ℝ} (h : |α - β| < 2 * π / 3) :
    dist (angle_to_point (1 / √3) α) (angle_to_point (1 / √3) β) ≠ 1 := by
  intro h1
  have hsq := dist_angle_to_point_sq (1 / √3) α β
  rw [h1, div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)] at hsq
  have hcos : cos (α - β) = -(1 / 2) := by linarith
  have hlt := cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg (α - β)) (by linarith [pi_pos] : 2 * π / 3 ≤ π) h
  rw [cos_abs, cos_two_pi_div_three, hcos] at hlt
  exact lt_irrefl _ hlt

/-- The arc of the circle of radius `1/√3` swept by the angles in `[0, 2π/3)`: one third of the circle. -/
noncomputable def arc : Set (EuclideanSpace ℝ (Fin 2)) :=
  angle_to_point (1 / √3) '' Set.Ico 0 (2 * π / 3)

/-- The arc lies on the circle of radius `1/√3`. -/
theorem arc_subset_circle : arc ⊆ Circle (1 / √3) := by
  rintro _ ⟨α, -, rfl⟩
  show ‖angle_to_point (1 / √3) α‖ = 1 / √3
  exact norm_angle_to_point (by positivity) α

/-- The arc contains no two points at distance 1. -/
theorem arc_unit_safe : is_unit_safe arc := by
  rintro _ ⟨α, hα, rfl⟩ _ ⟨β, hβ, rfl⟩
  apply dist_ne_one_of_abs_sub_lt
  rw [abs_lt]
  constructor <;> linarith [hα.1, hα.2, hβ.1, hβ.2]

/-- The arc has angular measure at least `2π/3`. -/
theorem two_pi_div_three_le_measure_arc : 2 * π / 3 ≤ color_measure (1 / √3) arc := by
  have hsub : Set.Ico 0 (2 * π / 3) ⊆ angle_to_point (1 / √3) ⁻¹' arc ∩ Set.Ico 0 (2 * π) := by
    intro α hα
    exact ⟨(show angle_to_point (1 / √3) α ∈ arc from Set.mem_image_of_mem _ hα), hα.1,
      by linarith [hα.2, pi_pos]⟩
  have hfin : volume (angle_to_point (1 / √3) ⁻¹' arc ∩ Set.Ico 0 (2 * π)) ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)
      (measure_mono Set.inter_subset_right)
  have h := ENNReal.toReal_mono hfin (measure_mono hsub)
  rw [Real.volume_Ico, ENNReal.toReal_ofReal (by linarith [pi_pos])] at h
  simpa [color_measure] using h

/-- **(b), radius `1/√3`** (the radius of the paper's worked example). The density bound fails for the arc of 120°:
it has no two points at distance 1, and its angular measure is at least `2π/3`, which is not below `π/3`. -/
theorem density_bound_false_at_inv_sqrt_three : ¬ SafeDensity (1 / √3) arc := by
  intro h
  have h1 := h arc_unit_safe
  have h2 := two_pi_div_three_le_measure_arc
  linarith [pi_pos]

/-! ## (c) The theorem uses no geometry -/

/-- Six real numbers, each below `π/3`, add up to less than `2π`. -/
theorem six_numbers (f : Fin 6 → ℝ) (h : ∀ i, f i < π / 3) : ∑ i, f i < 2 * π := by
  calc ∑ i, f i < ∑ _i : Fin 6, π / 3 :=
        Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ => h i)
    _ = 2 * π := by simp; ring

/-- **(c)** The statement of `coloring_collision`, proved again in one line from `six_numbers`. The colouring enters
only to hand each class's "no two points at distance 1" (`C.proper i`) to the assumed bound `h_safe`. Circles,
distances and angles play no part: the whole content of the theorem is its hypothesis. -/
theorem headline_from_six_numbers (r : ℝ) (C : SixColoring r) (h_safe : ∀ i, SafeDensity r (C.color i)) :
    (∑ i, color_measure r (C.color i)) < 2 * π :=
  six_numbers _ fun i => h_safe i (C.proper i)

/-! ## (d) Three colours suffice on the circle of radius `1/√3` -/

/-- A point of the plane as a complex number, to read off its angle. -/
noncomputable def toC (p : EuclideanSpace ℝ (Fin 2)) : ℂ := ⟨p 0, p 1⟩

/-- The angle of a point, in `[0, 2π)`. -/
noncomputable def ang (p : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  if Complex.arg (toC p) < 0 then Complex.arg (toC p) + 2 * π else Complex.arg (toC p)

theorem ang_mem (p : EuclideanSpace ℝ (Fin 2)) : ang p ∈ Set.Ico 0 (2 * π) := by
  unfold ang
  split_ifs with h
  · exact ⟨by linarith [Complex.neg_pi_lt_arg (toC p), pi_pos], by linarith⟩
  · exact ⟨not_lt.mp h, by linarith [Complex.arg_le_pi (toC p), pi_pos]⟩

/-- A point of the circle of radius `r` is the point at its own angle. -/
theorem angle_to_point_ang {r : ℝ} {p : EuclideanSpace ℝ (Fin 2)} (hp : ‖p‖ = r) :
    angle_to_point r (ang p) = p := by
  have hn : ‖toC p‖ = r := by
    rw [← hp, EuclideanSpace.norm_eq, Complex.norm_eq_sqrt_sq_add_sq]
    simp [toC, Fin.sum_univ_two]
  have hc : cos (ang p) = cos (Complex.arg (toC p)) := by
    unfold ang; split_ifs <;> simp [cos_add_two_pi]
  have hs : sin (ang p) = sin (Complex.arg (toC p)) := by
    unfold ang; split_ifs <;> simp [sin_add_two_pi]
  have h0 : r * cos (Complex.arg (toC p)) = p 0 := by
    rw [← hn, Complex.norm_mul_cos_arg]; rfl
  have h1 : r * sin (Complex.arg (toC p)) = p 1 := by
    rw [← hn, Complex.norm_mul_sin_arg]; rfl
  ext i
  fin_cases i
  · simp [angle_to_point, hc, h0]
  · simp [angle_to_point, hs, h1]

/-- Colour `k` for `k = 0, 1, 2` is the set of points of the circle of radius `1/√3` whose angle lies in
`[2πk/3, 2π(k+1)/3)`: three arcs of 120°. Colours 3, 4 and 5 are empty. -/
noncomputable def arcClass (k : Fin 6) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {p | ‖p‖ = 1 / √3 ∧ (k : ℕ) < 3 ∧ ang p ∈ Set.Ico (2 * π * k / 3) (2 * π * (k + 1) / 3)}

/-- No colour class contains two points at distance 1. -/
theorem arcClass_unit_safe (k : Fin 6) : is_unit_safe (arcClass k) := by
  rintro u ⟨hu, -, hku⟩ v ⟨hv, -, hkv⟩ h
  refine dist_ne_one_of_abs_sub_lt (α := ang u) (β := ang v) ?_ ?_
  · rw [abs_lt]
    constructor <;> nlinarith [hku.1, hku.2, hkv.1, hkv.2]
  · rw [angle_to_point_ang hu, angle_to_point_ang hv]
    exact h

/-- **(d)** A proper colouring of the circle of radius `1/√3`, as a term of this repository's own structure
`SixColoring`: the classes lie on the circle, cover it, and none contains two points at distance 1. -/
noncomputable def threeArcs : SixColoring (1 / √3) where
  color := arcClass
  on_circle k p hp := hp.1
  covering := by
    ext p
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨k, hk⟩; exact hk.1
    · intro hp
      have hp' : ‖p‖ = 1 / √3 := hp
      obtain ⟨h0, h2⟩ := ang_mem p
      by_cases ha : ang p < 2 * π / 3
      · exact ⟨0, hp', by norm_num, by simp; constructor <;> linarith⟩
      · by_cases hb : ang p < 4 * π / 3
        · exact ⟨1, hp', by norm_num, by simp; constructor <;> linarith⟩
        · exact ⟨2, hp', by norm_num, by norm_num; constructor <;> linarith⟩
  proper := arcClass_unit_safe

/-- **(d), continued.** That colouring uses three colours: classes 3, 4 and 5 are empty. So the circle the paper
works on needs at most three colours, not seven. -/
theorem threeArcs_three_colours (k : Fin 6) (hk : 3 ≤ (k : ℕ)) : threeArcs.color k = ∅ := by
  apply Set.eq_empty_of_forall_notMem
  intro p hp
  have hp' : p ∈ arcClass k := hp
  obtain ⟨-, hlt, -⟩ := hp'
  omega

/-! ## Remark: the negative radius -/

/-- For `r < 0` the set `Circle r` is empty: no point has negative norm. -/
theorem circle_of_negative_radius {r : ℝ} (hr : r < 0) : Circle r = ∅ := by
  apply Set.eq_empty_of_forall_notMem
  intro p hp
  have hp' : ‖p‖ = r := hp
  linarith [norm_nonneg p]

/-- For `r < 0`, six empty classes form a `SixColoring r` (of the empty set). -/
def emptyColouring {r : ℝ} (hr : r < 0) : SixColoring r where
  color _ := ∅
  on_circle _ := Set.empty_subset _
  covering := by rw [circle_of_negative_radius hr]; simp
  proper _ := fun u hu => absurd hu (Set.notMem_empty u)

/-- **Remark.** For `r < 0` the empty colouring satisfies the hypothesis of `coloring_collision`. Together with (a),
this is the only situation in which that hypothesis holds: an empty "circle" with nothing coloured, where the
conclusion says `0 < 2π`. -/
theorem emptyColouring_meets_hypothesis {r : ℝ} (hr : r < 0) :
    ∀ i, SafeDensity r ((emptyColouring hr).color i) := by
  intro i _
  have h0 : color_measure r (∅ : Set (EuclideanSpace ℝ (Fin 2))) = 0 := by simp [color_measure]
  show color_measure r ∅ < π / 3
  rw [h0]
  positivity

end Audit

/-! ## What each result rests on

Each line below prints `[propext, Classical.choice, Quot.sound]`: Lean's three standard axioms and nothing else. -/

#print axioms Audit.hypothesis_never_holds
#print axioms Audit.some_class_breaks_the_bound
#print axioms Audit.density_bound_false_at_quarter
#print axioms Audit.density_bound_false_at_inv_sqrt_three
#print axioms Audit.headline_from_six_numbers
#print axioms Audit.threeArcs
#print axioms Audit.threeArcs_three_colours
#print axioms Audit.emptyColouring_meets_hypothesis
