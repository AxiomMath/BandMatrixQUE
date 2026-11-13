module

public import BlockBand.Palm.MomentFlow.FlatTerm
public import BlockBand.Palm.MomentFlow.FlatArith

/-!
# The three clauses of `Flattening` along one good sample path

**`flat_clauses`**: with the local moment bounds `M_loc` for a version `Φ` (equal to `canonDatum` at
time `a`), bulk of every admissible centre (`nearBulk`), the window energies, `b ≤ C₂ N^{C₁ε}` and
`main ≤ C₂ N^{C₁ε} ℓ/w`, the three clauses of `Flattening` hold with `e = flatExcess(·, ω)`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Set Finset
open BlockBand.Internal.Contracts.CoareaPalm

variable {N : ℕ}

theorem flat_clauses {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (hN : 0 < N)
    {a c : ℝ} (hac : a ≤ c) (q : Fin N → ℂ) {r n : ℕ} {ω : FlowSample N}
    (hn : ω ∈ gapSet F a c n) {E r₀ ρ M Kw ce b main C₁ C₂ ε : ℝ} (hr₀ : 0 < r₀)
    (hKw : 0 < Kw) (hce : 0 < ce) (hWρ : Kw * cmW N ≤ ρ)
    {Φ : ℝ → Occ N → FlowSample N → ℝ} (h0 : ∀ ζ ∈ sector N r, Φ a ζ ω = canonDatum F a c q ω ζ)
    (hml : ∀ ξ ∈ sector N r, ∀ σ ∈ Icc a c, 0 ≤ Φ σ ξ ω ∧
      ((∀ k : Fin N, 0 < ξ k → ∀ σ' ∈ Icc a c, |flowEigenvalue F a ω σ' k - E| ≤ r₀ / 2) →
        Φ σ ξ ω ≤ b))
    (hnb : ∀ σ₀ ∈ Icc a c, ∀ k₀ : Fin N, |flowEigenvalue F a ω σ₀ k₀ - E| ≤ M * cmW N / N →
      ω ∈ nearBulk F a c E (r₀ / 16) ρ k₀)
    (hen : ∀ σ₀ ∈ Icc a c, ∀ k₀ k : Fin N, |flowEigenvalue F a ω σ₀ k₀ - E| ≤ M * cmW N / N →
      (labelDist k₀ k : ℝ) ≤ 4 * (Kw * cmW N) → ∀ v ∈ Icc a c,
        |flowEigenvalue F a ω v k - flowEigenvalue F a ω σ₀ k₀| ≤
          (3 + 10 * Kw / ce) * cmW N / N)
    (hbN : b ≤ C₂ * (N : ℝ) ^ (C₁ * ε))
    (hmain : main ≤ C₂ * (N : ℝ) ^ (C₁ * ε) * ((cmEll N : ℝ) / cmW N))
    (hC₂ : C₂ = 1 + (3 + 10 * Kw / ce) / Kw) :
    ∀ σ₀ ∈ Icc a c, ∀ k₀ : Fin N,
      |flowEigenvalue F a ω σ₀ k₀ - E| ≤ M * cmW N / N →
      (∀ ζ ∈ sector N r, (rampDist (k₀ : ℕ) ζ : ℝ) ≤ Kw * cmW N →
        0 ≤ Φ a ζ ω ∧ Φ a ζ ω ≤ C₂ * (N : ℝ) ^ (C₁ * ε)) ∧
      (∀ u ∈ Icc a c, ∀ j : Fin N, (labelDist j k₀ : ℝ) ≤ 4 * (Kw * cmW N) →
        |flowEigenvalue F a ω u j - E| ≤ C₂ * (M + Kw) * cmW N / N) ∧
      ∀ g h : ℝ → Occ N → ℝ, ShortSol F a c ω (cmEll N) r g → ShortSol F a c ω (cmEll N) r h →
        (∀ ζ ∈ sector N r, g a ζ = avFlat (ramp (Kw * cmW N) (k₀ : ℕ)) (fun ζ' => Φ a ζ' ω) ζ) →
        (∀ ζ ∈ sector N r, h a ζ = Φ a ζ ω) →
        ∀ u ∈ Icc a c, ∀ ζ ∈ sector N r,
          |g u ζ - avFlat (ramp (Kw * cmW N) (k₀ : ℕ)) (h u) ζ| ≤
            C₂ * (N : ℝ) ^ (C₁ * ε) * ((cmEll N : ℝ) / cmW N) +
              flatExcess F a c q (cmEll N) r n E (r₀ / 16) ρ (Kw * cmW N) main u ω := by
  intro σ₀ hσ₀ k₀ hk₀
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hnb₀ := hnb σ₀ hσ₀ k₀ hk₀
  have hwN : 0 < cmW N / N := div_pos (Real.rpow_pos_of_pos hNr _) hNr
  have hM0 : 0 ≤ M := by
    by_contra hM
    have h1 : M * cmW N / N < 0 := by
      rw [mul_div_assoc]; exact mul_neg_of_neg_of_pos (not_le.1 hM) hwN
    linarith [(abs_nonneg _).trans hk₀]
  refine ⟨fun ζ hζ hrd => ?_, fun u hu j hj => ?_, fun g h hg hh hg0 hh0 u hu ζ hζ => ?_⟩
  · obtain ⟨hpos, hbd⟩ := hml ζ hζ a ⟨le_rfl, hac⟩
    have hbk := bulk_of_nearBulk hnb₀ (hrd.trans hWρ)
    exact ⟨hpos, (hbd fun k hk σ' hσ' => (hbk k hk σ' hσ').trans (by linarith)).trans hbN⟩
  · have h1 := hen σ₀ hσ₀ k₀ j hk₀ (by rw [labelDist_comm]; exact hj) u hu
    have h3 := abs_sub_le (flowEigenvalue F a ω u j) (flowEigenvalue F a ω σ₀ k₀) E
    have h4 := abs_sub_comm (flowEigenvalue F a ω σ₀ k₀) E
    have key := flat_energy_alg hM0 hKw hce hwN
    rw [← hC₂] at key
    have e1 : M * cmW N / N = M * (cmW N / N) := by ring
    have e2 : (3 + 10 * Kw / ce) * cmW N / N = (3 + 10 * Kw / ce) * (cmW N / N) := by ring
    have e3 : C₂ * (M + Kw) * cmW N / N = C₂ * (M + Kw) * (cmW N / N) := by ring
    rw [e3]
    rw [e1] at hk₀
    rw [e2] at h1
    linarith
  · have hgeq := shortSol_eq_fwdC hF hN hac (cmEll N) r n
      (flatDatum F a c q (Kw * cmW N) k₀) hn hg (fun ζ' hζ' => by
        rw [hg0 ζ' hζ']; simp only [flatDatum, avFlat, h0 ζ' hζ'])
    have hheq := shortSol_eq_shortC hF hN hac q (cmEll N) r n hn hh
      (fun ζ' hζ' => (hh0 ζ' hζ').trans (h0 ζ' hζ'))
    have hterm := term_le_flatExcess (F := F) (a := a) (c := c) (q := q) (ℓ := cmEll N) (n := n)
      (W := Kw * cmW N) (main := main) (v := u) (E := E) (κ := r₀ / 16) (ρ := ρ) hζ hnb₀
    have havg : avFlat (ramp (Kw * cmW N) (k₀ : ℕ)) (h u) ζ =
        avFlat (ramp (Kw * cmW N) (k₀ : ℕ)) (shortC F a c q (cmEll N) r n u ω) ζ := by
      simp only [avFlat, hheq u hu ζ hζ]
    rw [hgeq u hu ζ hζ, havg]
    have hmax := le_max_left (|fwdC F a c (cmEll N) r n (flatDatum F a c q (Kw * cmW N) k₀) u ω ζ -
      avFlat (ramp (Kw * cmW N) (k₀ : ℕ)) (shortC F a c q (cmEll N) r n u ω) ζ| - main) 0
    linarith

end BlockBand.Palm.MomentFlow
