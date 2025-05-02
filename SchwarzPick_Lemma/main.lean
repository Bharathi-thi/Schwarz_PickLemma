import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.UnitDisc.Basic
--import Mathlib.Analysis.Complex.OpenMapping

import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Analytic.Basic

open Metric Set Function Filter TopologicalSpace Complex

open scoped ComplexConjugate

open scoped Topology

namespace Complex

section Space

set_option maxHeartbeats 5000000

variable {f : ℂ → ℂ} {z : ℂ}

/-- A biholomorphism on the unit disc is a bijective holomorphic map with a holomorphic inverse. -/
def Biholomorphism_on_unit_disc (f : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ f (ball 0 1) ∧
  ∃ (g : ℂ → ℂ), DifferentiableOn ℂ g (ball 0 1) ∧
    MapsTo g (ball 0 1) (ball 0 1) ∧
    (∀ z ∈ ball 0 1, f (g z) = z) ∧
    (∀ w ∈ ball 0 1, g (f w) = w)

/-- If `f` is a biholomorphism on the unit disc fixing 0, then `g(f(0)) = 0`. -/
lemma inverse_at_zero {f g : ℂ → ℂ}
    (h₀ : f 0 = 0) (hg_right_inv : ∀ w ∈ ball 0 1, g (f w) = w) :
    g 0 = 0 := by
      have h_gf0 : g (f 0) = 0 := hg_right_inv 0 (mem_ball_self zero_lt_one)
      rw [h₀] at h_gf0
      exact h_gf0

/-- If `f` and its inverse `g` both map the unit disc into itself and fix 0, then they preserve norms. -/
lemma norm_preserved
    (f g : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (ball 0 1)) (hg : DifferentiableOn ℂ g (ball 0 1))
    (h_maps_f : MapsTo f (ball 0 1) (ball 0 1))
    (h_maps_g : MapsTo g (ball 0 1) (ball 0 1))
    (h₀ : f 0 = 0) (hg₀ : g 0 = 0)
    (hg_right_inv : ∀ w ∈ ball 0 1, g (f w) = w) :
    ∀ z ∈ ball 0 1, ‖f z‖ = ‖z‖ := by
    have h_norm_le : ∀ z ∈ ball 0 1, ‖f z‖ ≤ ‖z‖ :=
      fun z hz => norm_le_norm_of_mapsTo_ball_self hf h_maps_f h₀ (mem_ball_zero_iff.mp hz)
    have h_norm_ge : ∀ z ∈ ball 0 1, ‖z‖ ≤ ‖f z‖ := by
      intro z hz
      have h_fz_in_ball : f z ∈ ball 0 1 := h_maps_f hz
      have h_fgz : g (f z) = z := hg_right_inv z hz
      have h_fz_in_ball : f z ∈ ball 0 1 := h_maps_f hz
      have h2_spec : ‖g (f z)‖ ≤ ‖f z‖ := norm_le_norm_of_mapsTo_ball_self hg h_maps_g hg₀ (mem_ball_zero_iff.mp h_fz_in_ball)
      have h_fgz : g (f z) = z := hg_right_inv z hz
      rw [h_fgz] at h2_spec
      exact h2_spec
    intro z hz
    exact le_antisymm (h_norm_le z hz) (h_norm_ge z hz)


lemma Differentiable_on_punctured_ball_div_z
  (hf : DifferentiableOn ℂ f (ball 0 1 \ {0})) (h_inv : DifferentiableOn ℂ (fun z : ℂ ↦ z⁻¹) (ball 0 1 \ {0})) :
  DifferentiableOn ℂ (fun z ↦ f z * z⁻¹) (ball 0 1 \ {0}) := by
  apply DifferentiableOn.mul hf h_inv



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {U : Set E} {g : E → ℂ}

lemma function_unit_modulus
  (hg : DifferentiableOn ℂ g (ball 0 1 \ {0}))
  (h_mod : ∀ z ∈ ball 0 1 \ {0}, ‖g z‖ = 1) :
  ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ z ∈ ball 0 1 \ {0}, g z = c := by sorry

/-- Main statement: A biholomorphism of the unit disc fixing 0 is a rotation. -/
theorem Aut_unit_disc_fixes_origin
    (h_maps : MapsTo f (ball 0 1) (ball 0 1))
    (hd : Biholomorphism_on_unit_disc f)
    (h₀ : f 0 = 0) :
        ∃ (w : ℂ), ‖w‖ = 1 ∧ ∀ (z : ℂ), ‖z‖ < 1 → f z = w * z := by
  obtain ⟨hf, g, hg, hg_maps, hg_left_inv, hg_right_inv⟩ := hd
  have hg₀ : g 0 = 0 := inverse_at_zero h₀ hg_right_inv
  have h_norm_preserved := norm_preserved f g hf hg h_maps hg_maps h₀ hg₀ hg_right_inv
  let h := fun z : ℂ ↦ f z * z⁻¹
  sorry










/- # Automorphism group of the open unit disc

It states that any biholomorphic map from the open unit disc to itself is a composition of a rotation and a Mobius transformation is of the form (a - z) / (1 - conj a * z). We need sveral basic lemma's to describe the automorphism group of Δ. First we show that the map (fun z ↦ (a - z) / (1 - conj a * z)) is an automorphism of the unit disc. -/
lemma Mobius_mapOn_unit_disc_is_automorphism (a : ℂ) (ha : ‖a‖ < 1) : Biholomorphism_on_unit_disc (fun z ↦ (a - z) / (1 - conj a * z)) := by
  sorry


/-The next lemma shows that the composition of two biholomorphisms is also a biholomorphism. -/

lemma Biholomorphism_on_unit_disc.comp
  {f g : ℂ → ℂ}
  (hf : Biholomorphism_on_unit_disc f)
  (hg : Biholomorphism_on_unit_disc g) :
  Biholomorphism_on_unit_disc (g ∘ f) := by
  sorry

theorem Aut_group_of_unit_disc : ∀ (f : ℂ → ℂ),
      (MapsTo f (ball 0 1) (ball 0 1)) → Biholomorphism_on_unit_disc f → ∃ w : ℂ, ‖w‖ = 1 ∧ ∃ a : ℂ, ‖a‖ < 1 ∧ ∀ z ∈ ball 0 1, f z = w * (a - z) / (1 - conj a * z) := by
      intros f h_maps hf
      let a := f 0
      let g := fun z : ℂ ↦ (a - z) / (1 - conj a * z)
      have ha : ‖a‖ < 1 := by
        -- Prove that ‖a‖ < 1 using the fact that f maps the unit disc into itself
        exact mem_ball_zero_iff.mp (h_maps (mem_ball_self zero_lt_one))
      have hg : Biholomorphism_on_unit_disc g :=
        Mobius_mapOn_unit_disc_is_automorphism a ha
      -- Let h = g ∘ f
      let h := g ∘ f
      -- h is a biholomorphism on the unit disc
      have hh : Biholomorphism_on_unit_disc h :=
        Biholomorphism_on_unit_disc.comp hf hg
      -- And h(0) = g(f(0)) = g(a)
      have h0 : h 0 = g a := rfl
      simp only [g, Function.comp_apply] at h0
      simp only [div_self] at h0
      · simp only [sub_self, zero_div] at h0
        have gfa0 : h 0 = 0 := by
          rw [h0]
        obtain ⟨w, hw₁, hw₂⟩ :=
          Aut_unit_disc_fixes_origin
          (fun z hz =>
            let ⟨g, hg_diff, hg_maps, hg_left_inv, hg_right_inv⟩ := hh
            hg_maps (f z) (h_maps z hz))
            hh
            gfa0
        use w
        use hw₁
        use a
        use ha
        intro z hz
        specialize hw₂ z hz
        simp only [Function.comp_apply, g] at hw₂
        field_simp [ne_of_lt (lt_of_lt_of_le (norm_lt_one_iff_mem_ball.mpr hz) (by norm_num : 1 ≤ 1))]
        ring
