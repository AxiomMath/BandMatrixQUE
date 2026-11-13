module

public import BlockBand.Critical.Herglotz.Far
public import BlockBand.Critical.Herglotz.NearLaw

/-!
# Assembly of the Herglotz tail lemma from the real-constant step

`herglotzTail_of_farPartSmall`: under `IsCanonicalCauchy` and the hypotheses of the Herglotz tail
lemma, `FarPartSmall` implies the conclusion of the lemma. Proof: convergence together
(`tendstoInDistribution_of_forall_approx`) with approximants the near parts
(`HerglotzTailHypotheses.tendstoInDistribution_nearPart`), whose canonical limits
`smoothCauchy Ξ n` converge in probability to `𝖢_r` in `(Fin k → Matrix) × C(K, Matrix)`.
The far part is controlled by polarization (`norm_apply_le_polarization`), `FarPartSmall` at
finitely many vectors, and the far-variation bound `farPart_sub_le` with the escaped mass
(`HerglotzTailHypotheses.eventually_measure_tailMass_le`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped Matrix NNReal ENNReal ComplexOrder

namespace BlockBand.Critical.Herglotz

open scoped JV
open BlockBand.Internal.Contracts.CriticalEntire

variable {r : ℕ}

/-- **Conclusion of the real-constant step** (`C = 0` and no escaped imaginary mass, at finite
`N`). For every
`v ∈ ℂ^r` and `ε, η > 0` there is `Y > 0` with: eventually in `n : ℕ`, eventually in `N`,
`P_N*(ε ≤ |v^* (F_N - near_{N,n})(iY) v|) ≤ η`. -/
def FarPartSmall {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    (F : ∀ N, Ω N → AtomicHerglotz r) : Prop :=
  ∀ (v : Fin r → ℂ) (ε η : ℝ), 0 < ε → 0 < η → ∃ Y : ℝ, 0 < Y ∧ ∀ᶠ n : ℕ in atTop,
    ∀ᶠ N in atTop,
      P N {ω | ε ≤ ‖quad (farPart (F N ω) n ((Y : ℂ) * Complex.I)) v‖} ≤ ENNReal.ofReal η

/-- The four polarization constants `1, -1, i, -i`. -/
def polConst (k : Fin 4) : ℂ := ![1, -1, Complex.I, -Complex.I] k

theorem norm_polConst (k : Fin 4) : ‖polConst k‖ = 1 := by
  fin_cases k <;> simp [polConst]

theorem norm_apply_le_polConst (M : Matrix (Fin r) (Fin r) ℂ) (i j : Fin r) :
    ‖M i j‖ ≤ (∑ k : Fin 4, ‖quad M (polVec i j (polConst k))‖) / 4 := by
  have := norm_apply_le_polarization M i j
  simpa [Fin.sum_univ_four, polConst] using this

section Main

variable {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)] {P : ∀ N, Measure (Ω N)}
  [∀ N, IsProbabilityMeasure (P N)] {F : ∀ N, Ω N → AtomicHerglotz r} {Ω' : Type}
  [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {Ξ : Ω' → VaguePointMeasure (ℝ × (Fin r → ℂ))} {C : Ω' → ℂ → Matrix (Fin r) (Fin r) ℂ}

/-- **Assembly.** For a realization `IsCanonicalCauchy r P' Ξ C` of `𝖢_r` and random atomic
Herglotz functions satisfying the hypotheses of the Herglotz tail lemma, the conclusion of the
real-constant step (`FarPartSmall`) implies the conclusion of the lemma: for every `k`, real points `x` and
compact `K ⊆ {Im z > 0}`, `jointValues F_N x K ⇒ jointValues 𝖢_r x K`. -/
theorem herglotzTail_of_farPartSmall (hC : IsCanonicalCauchy r P' Ξ C)
    (h : HerglotzTailHypotheses r P F P' Ξ) (hfar : FarPartSmall P F) :
    HerglotzTailConclusion r P F P' C := by
  intro k x K hK hKs
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hΞ := hC.decorated
  obtain ⟨c, hc, hKc⟩ := exists_im_lower_bound hK hKs
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  set R₀ : ℝ := |R| + ∑ a, |x a| + 1 with hR₀
  have hxR : ∀ a, |x a| ≤ R₀ := fun a => by
    have := Finset.single_le_sum (f := fun a => |x a|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ a)
    have := abs_nonneg R
    linarith
  have hKR : ∀ z ∈ K, ‖z‖ ≤ R₀ := fun z hz => by
    have := hR z hz
    have := le_abs_self R
    have := Finset.sum_nonneg fun a (_ : a ∈ Finset.univ) => abs_nonneg (x a)
    linarith
  -- the sequences
  set X : ℕ → ∀ N, Ω N → JointValues r k K :=
    fun n N ω => jointValues (nearPart (atomMeasure (F N ω)) n) x K with hXdef
  set X' : ℕ → Ω' → JointValues r k K :=
    fun n ω => jointValues (nearPart (canonMeasure (Ξ ω)) n) x K with hX'def
  set Z : Ω' → JointValues r k K := fun ω => jointValues (C ω) x K with hZdef
  have hX : ∀ n : ℕ, TendstoInDistribution (X n) atTop (X' n) P P' := fun n =>
    h.tendstoInDistribution_nearPart hΞ (Nat.cast_nonneg n) x hK hKs
  have hY : ∀ N, AEMeasurable (fun ω => jointValues (F N ω).eval x K) (P N) := fun N =>
    (measurable_jointValues hK x (measurable_eval_at (h.measurable_eval N))
      fun ω => (continuousOn_eval _).mono hKs).aemeasurable
  -- canonical near parts converge in probability to `𝖢_r`
  have hTIM : TendstoInMeasure P' X' atTop Z := by
    rw [tendstoInMeasure_iff_dist]
    intro ε hε
    set A : ℕ → Set Ω' := fun n => {ω | ∃ z ∈ K, ∃ i j : Fin r,
      ε / 2 ≤ ‖smoothCauchy r (Ξ ω) n z i j - C ω z i j‖} with hA
    set B : ℕ → Fin k × Fin r × Fin r → Set Ω' := fun n t => {ω | ε / 2 ≤
      dist (smoothCauchy r (Ξ ω) n (x t.1) t.2.1 t.2.2) (C ω (x t.1) t.2.1 t.2.2)} with hB
    have hsub : ∀ n, {ω | ε ≤ dist (X' n ω) (Z ω)} ⊆ A n ∪ ⋃ t, B n t := by
      intro n ω hω
      by_contra hcon
      simp only [mem_union, mem_iUnion, not_or, not_exists, hA, hB, mem_ofPred_eq, not_le]
        at hcon
      obtain ⟨h1, h2⟩ := hcon
      have hcont := continuousOn_nearPart (canonMeasure (Ξ ω)) (n : ℝ) hc hKc hKR
      have hd := dist_jointValues_le (G := nearPart (canonMeasure (Ξ ω)) n) (G' := C ω) hcont
        ((hC.continuousOn ω).mono hKs) x (half_pos hε).le
        (fun a i j => by
          rw [nearPart_canonMeasure, ← dist_eq_norm]; exact (h2 (a, i, j)).le)
        (fun z hz i j => by
          rw [nearPart_canonMeasure]
          exact le_of_lt (not_le.1 fun hle => h1 z ⟨hz, i, j, hle⟩))
      simp only [mem_ofPred_eq] at hω
      linarith [half_lt_self hε]
    have hlimA : Tendsto (fun n => P' (A n)) atTop (𝓝 0) :=
      (hC.tendsto_smoothCauchy_locallyUniform hK hKs (half_pos hε)).comp
        tendsto_natCast_atTop_atTop
    have hlimB : ∀ t, Tendsto (fun n => P' (B n t)) atTop (𝓝 0) := fun t =>
      ((tendstoInMeasure_iff_dist.1 (hC.tendstoInMeasure_smoothCauchy_real (x t.1) t.2.1 t.2.2))
        (ε / 2) (half_pos hε)).comp tendsto_natCast_atTop_atTop
    have hsum : Tendsto (fun n => P' (A n) + ∑ t, P' (B n t)) atTop (𝓝 0) := by
      have := hlimA.add (tendsto_finsetSum (Finset.univ : Finset (Fin k × Fin r × Fin r))
        fun t _ => hlimB t)
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => bot_le)
      fun n => ?_
    exact (measure_mono (hsub n)).trans ((measure_union_le _ _).trans
      (add_le_add le_rfl (measure_iUnion_fintype_le _ _)))
  have hX' : TendstoInDistribution X' atTop Z (fun _ => P') P' :=
    hTIM.tendstoInDistribution fun n => (hX n).aemeasurable_limit
  -- closeness of `F_N` and its near part
  have hclose : ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop, ∀ᶠ N in atTop,
      P N {ω | ε ≤ dist (jointValues (F N ω).eval x K) (X n N ω)} ≤ ENNReal.ofReal η := by
    intro ε hε η hη
    set m : ℕ := Fintype.card (Fin r × Fin r × Fin 4) with hm
    set η' : ℝ := η / (m + 1) with hη'
    have hη'0 : 0 < η' := by positivity
    choose Y hYpos hYev using fun t : Fin r × Fin r × Fin 4 =>
      hfar (polVec t.1 t.2.1 (polConst t.2.2)) (ε / 4) η' (by positivity) hη'0
    set R₁ : ℝ := R₀ + ∑ t, Y t with hR₁
    have hYle : ∀ t, Y t ≤ ∑ t, Y t := fun t =>
      Finset.single_le_sum (f := Y) (fun t _ => (hYpos t).le) (Finset.mem_univ t)
    have hR₀0 : 0 < R₀ := by
      have := abs_nonneg R
      have := Finset.sum_nonneg fun a (_ : a ∈ Finset.univ) => abs_nonneg (x a)
      linarith
    have hR₁0 : 0 < R₁ := by
      have := Finset.sum_nonneg fun t (_ : t ∈ Finset.univ) => (hYpos t).le
      linarith
    have hR₀R₁ : R₀ ≤ R₁ := by
      have := Finset.sum_nonneg fun t (_ : t ∈ Finset.univ) => (hYpos t).le
      linarith
    set s : ℝ := ε / (4 * (4 * (8 * R₁))) with hs
    have hs0 : 0 < s := by positivity
    have hev_n : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ n ∧ 2 * R₁ ≤ n := by
      filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (1 : ℝ),
        tendsto_natCast_atTop_atTop.eventually_ge_atTop (2 * R₁)] with n h1 h2
      exact ⟨h1, h2⟩
    filter_upwards [hev_n, Filter.eventually_all.2 hYev,
      h.eventually_measure_tailMass_le hΞ hs0 hη'0] with n hn hnY hnT
    filter_upwards [Filter.eventually_all.2 hnY, hnT] with N hNY hNT
    have hsub : {ω | ε ≤ dist (jointValues (F N ω).eval x K) (X n N ω)} ⊆
        (⋃ t, {ω | ε / 4 ≤ ‖quad (farPart (F N ω) n ((Y t : ℂ) * Complex.I))
          (polVec t.1 t.2.1 (polConst t.2.2))‖}) ∪ {ω | s ≤ tailMass (F N ω) n} := by
      intro ω hω
      by_contra hcon
      simp only [mem_union, mem_iUnion, not_or, not_exists, mem_ofPred_eq, not_le] at hcon
      obtain ⟨h1, h2⟩ := hcon
      set G := F N ω
      -- entry bound for the far part at points of norm `≤ R₀`
      have hent : ∀ z : ℂ, ‖z‖ ≤ R₀ → ∀ i j, ‖farPart G n z i j‖ ≤ ε / 2 := by
        intro z hz i j
        refine (norm_apply_le_polConst _ i j).trans ?_
        have hq : ∀ q : Fin 4, ‖quad (farPart G n z) (polVec i j (polConst q))‖ ≤
            ε / 4 + 4 * (8 * R₁ * tailMass G n) := by
          intro q
          set t : Fin r × Fin r × Fin 4 := (i, j, q)
          have hYt : ‖(Y t : ℂ) * Complex.I‖ ≤ R₁ := by
            rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos (hYpos t)]
            linarith [hYle t]
          have hdec : quad (farPart G n z) (polVec i j (polConst q)) =
              quad (farPart G n ((Y t : ℂ) * Complex.I)) (polVec i j (polConst q)) +
                quad (farPart G n z - farPart G n ((Y t : ℂ) * Complex.I))
                  (polVec i j (polConst q)) := by
            rw [quad_sub]; ring
          rw [hdec]
          refine (norm_add_le _ _).trans (add_le_add (h1 t).le ?_)
          refine (norm_quad_le _ _ fun k l => farPart_sub_le G hn.1 hn.2
            (hz.trans hR₀R₁) hYt k l).trans ?_
          have h2' := sum_norm_polVec_le i j (norm_polConst q)
          have hT0 := tailMass_nonneg G n
          have : (∑ k, ‖polVec i j (polConst q) k‖) ^ 2 ≤ 4 := by
            have := Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) =>
              norm_nonneg (polVec i j (polConst q) k)
            nlinarith
          have hb : 0 ≤ 8 * R₁ * tailMass G n := by positivity
          nlinarith
        have hsum := Finset.sum_le_sum fun q (_ : q ∈ Finset.univ) => hq q
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
        have hT : 4 * (4 * (8 * R₁ * tailMass G n)) < ε := by
          have := h2
          rw [hs, lt_div_iff₀ (by positivity)] at this
          linarith
        have : (∑ q : Fin 4, ‖quad (farPart G n z) (polVec i j (polConst q))‖) / 4 ≤
            (4 * (ε / 4 + 4 * (8 * R₁ * tailMass G n))) / 4 := by
          gcongr
          exact_mod_cast hsum
        linarith
      have hcont := continuousOn_nearPart (atomMeasure G) (n : ℝ) hc hKc hKR
      have hd := dist_jointValues_le (G := G.eval) (G' := nearPart (atomMeasure G) n)
        ((continuousOn_eval G).mono hKs) hcont x (half_pos hε).le
        (fun a i j => by
          rw [← Matrix.sub_apply]
          exact hent _ (by rw [Complex.norm_real, Real.norm_eq_abs]; exact hxR a) i j)
        (fun z hz i j => by
          rw [← Matrix.sub_apply]
          exact hent z (hKR z hz) i j)
      simp only [mem_ofPred_eq] at hω
      linarith [half_lt_self hε]
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    refine (add_le_add ((measure_iUnion_fintype_le _ _).trans
      (Finset.sum_le_sum fun t _ => hNY t)) hNT).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hm, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_add (by positivity) hη'0.le]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    rw [hη']
    field_simp
  exact tendstoInDistribution_of_forall_approx hY hX hX' hclose

end Main

end BlockBand.Critical.Herglotz
