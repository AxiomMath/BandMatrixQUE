module

public import BlockBand.SourceProcess.PhysApprox.B3Pins

/-!
# The seven clauses from coordinate-wise tested identities

The finite-`W` hypotheses are stated coordinate-wise on `CIdx = Gram entries ⊕ 𝒦 entries`
(`b3SummedErr c c'` with `cDrift`, `cCov`; `b3ConjErr` with `kConjCov`). This file states the
limit identities in the same coordinate-wise form and shows that they are exactly the seven
martingale clauses of `IsStoppedTestedComplexModel`; the five `𝒦` clauses (the part of the
extension specific to `𝒦`) come from the coordinates `Sum.inr`.

* `cComp c`: the compensated continuous part of coordinate `c`,
  `X_c(t) − J_c(t) − (X_c(0) − J_c(0)) − ∫_0^t cDrift_c(G_u) du`;
  `cComp_inl` (`= bornCompensated`, by `rfl`), `cComp_inr` (`= kCompensated`, zero drift).
* `cBr c c'`: `cComp c · cComp c' − ∫ cCov c c'`; `kBr ij kl`:
  `cComp ij · conj(cComp kl) − ∫ kConjCov ij kl`.
* `IsGramCoordTested`, `IsKCoordTested`: the coordinate identities stopped at a family of stops
  `σ L` (Gram, resp. `𝒦`-involving, coordinates).
* **`isStoppedTestedComplexModel_of_coord`**: the data fields of the model and the coordinate
  identities at `σ L = gramTraceStop G L` give `IsStoppedTestedComplexModel`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.Ident2

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.ClosedLimit
open scoped NNReal ComplexConjugate

variable {Ω : Type*} {K np : ℕ}

/-- **The compensated continuous part of the coordinate `c`.** -/
def cComp (b E s : ℝ) (τ m : Fin np → ℝ) (G : ℝ≥0 → Ω → GramState (SrcCol K (Fin np)))
    (Kc : ℝ≥0 → Ω → Matrix (Fin np) (Fin np) ℂ) (c : CIdx K np) (t : ℝ≥0) (ω : Ω) : ℂ :=
  cEntry c (G t ω - gramJ b s τ m t) (Kc t ω - kJ E s τ m t) -
    cEntry c (G 0 ω - gramJ b s τ m 0) (Kc 0 ω - kJ E s τ m 0) -
    ∫ u in Set.Ioc (0 : ℝ) t, cDrift b E c (G u.toNNReal ω)

/-- The bilinear bracket of two coordinates. -/
def cBr (b E s : ℝ) (τ m : Fin np → ℝ) (G : ℝ≥0 → Ω → GramState (SrcCol K (Fin np)))
    (Kc : ℝ≥0 → Ω → Matrix (Fin np) (Fin np) ℂ) (c c' : CIdx K np) (t : ℝ≥0) (ω : Ω) : ℂ :=
  cComp b E s τ m G Kc c t ω * cComp b E s τ m G Kc c' t ω -
    ∫ u in Set.Ioc (0 : ℝ) t, cCov b E c c' (G u.toNNReal ω)

/-- The conjugate bracket of two `𝒦` entries. -/
def kBr (b E s : ℝ) (τ m : Fin np → ℝ) (G : ℝ≥0 → Ω → GramState (SrcCol K (Fin np)))
    (Kc : ℝ≥0 → Ω → Matrix (Fin np) (Fin np) ℂ) (ij kl : Fin np × Fin np) (t : ℝ≥0) (ω : Ω) :
    ℂ :=
  cComp b E s τ m G Kc (Sum.inr ij) t ω * conj (cComp b E s τ m G Kc (Sum.inr kl) t ω) -
    ∫ u in Set.Ioc (0 : ℝ) t, kConjCov b E ij kl (G u.toNNReal ω)

variable {b E s : ℝ} {τ m : Fin np → ℝ} {G : ℝ≥0 → Ω → GramState (SrcCol K (Fin np))}
  {Kc : ℝ≥0 → Ω → Matrix (Fin np) (Fin np) ℂ}

theorem cComp_inl (e : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np)) :
    cComp b E s τ m G Kc (Sum.inl e) =
      bornCompensated (transportD0 b E) (srcSignature K (Fin np)) G
        (fun t _ => gramJ b s τ m t) e := rfl

theorem cComp_inr (ij : Fin np × Fin np) :
    cComp b E s τ m G Kc (Sum.inr ij) = kCompensated Kc (fun t _ => kJ E s τ m t) ij.1 ij.2 := by
  funext t ω
  simp [cComp, cEntry, cDrift, kCompensated]

theorem bracket_eq_cBr (e e' : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np)) :
    (fun t ω => bornCompensated (transportD0 b E) (srcSignature K (Fin np)) G
          (fun t _ => gramJ b s τ m t) e t ω *
        bornCompensated (transportD0 b E) (srcSignature K (Fin np)) G
          (fun t _ => gramJ b s τ m t) e' t ω -
        ∫ u in Set.Ioc (0 : ℝ) t, gramCovEntry (transportD0 b E) (srcSignature K (Fin np)) e e'
          (G u.toNNReal ω)) =
      cBr b E s τ m G Kc (Sum.inl e) (Sum.inl e') := rfl

theorem holo_eq_cBr (i j k l : Fin np) :
    (fun t ω => kCompensated Kc (fun t _ => kJ E s τ m t) i j t ω *
        kCompensated Kc (fun t _ => kJ E s τ m t) k l t ω) =
      cBr b E s τ m G Kc (Sum.inr (i, j)) (Sum.inr (k, l)) := by
  funext t ω
  simp only [cBr, cComp_inr, cCov, MeasureTheory.integral_zero, sub_zero]

theorem antiholo_eq_kBr (i j k l : Fin np) :
    (fun t ω => kCompensated Kc (fun t _ => kJ E s τ m t) i j t ω *
        conj (kCompensated Kc (fun t _ => kJ E s τ m t) k l t ω) -
        ∫ u in Set.Ioc (0 : ℝ) t, ((2 * etaZ b E ^ 2 * transportD0 b E : ℝ) : ℂ) *
          (G u.toNNReal ω).2 (Sum.inr i) (Sum.inr k) *
          gramC0 (G u.toNNReal ω).1 (G u.toNNReal ω).2 (srcSignature K (Fin np))
            (Sum.inr l) (Sum.inr j)) =
      kBr b E s τ m G Kc (i, j) (k, l) := by
  funext t ω
  simp only [kBr, cComp_inr, kConjCov]

theorem crossM_eq_cBr (i j : Fin np) (k l : SrcCol K (Fin np)) :
    (fun t ω => kCompensated Kc (fun t _ => kJ E s τ m t) i j t ω *
        bornCompensated (transportD0 b E) (srcSignature K (Fin np)) G
          (fun t _ => gramJ b s τ m t) (0, k, l) t ω -
        ∫ u in Set.Ioc (0 : ℝ) t, -(Complex.I * ((etaZ b E * transportD0 b E : ℝ) : ℂ)) *
          (G u.toNNReal ω).2 (Sum.inr i) l *
          gramC0 (G u.toNNReal ω).1 (G u.toNNReal ω).2 (srcSignature K (Fin np)) k (Sum.inr j)) =
      cBr b E s τ m G Kc (Sum.inr (i, j)) (Sum.inl (0, k, l)) := by
  funext t ω
  simp only [cBr, cComp_inr, cComp_inl, cCov, kGramCov, ↓reduceIte]

theorem crossB_eq_cBr (i j : Fin np) (k l : SrcCol K (Fin np)) :
    (fun t ω => kCompensated Kc (fun t _ => kJ E s τ m t) i j t ω *
        bornCompensated (transportD0 b E) (srcSignature K (Fin np)) G
          (fun t _ => gramJ b s τ m t) (1, k, l) t ω -
        ∫ u in Set.Ioc (0 : ℝ) t, -(Complex.I * ((etaZ b E * transportD0 b E : ℝ) : ℂ)) *
          (G u.toNNReal ω).2 (Sum.inr i) l *
          (gramC1 (G u.toNNReal ω).1 (G u.toNNReal ω).2 (srcSignature K (Fin np)))ᴴ k
            (Sum.inr j)) =
      cBr b E s τ m G Kc (Sum.inr (i, j)) (Sum.inl (1, k, l)) := by
  funext t ω
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp only [cBr, cComp_inr, cComp_inl, cCov, kGramCov, h10, ↓reduceIte]

/-!
## The coordinate-wise stopped tested identities
-/

/-- **The Gram coordinate identities** stopped at the family of stops `σ L`. -/
structure IsGramCoordTested [MeasurableSpace Ω] (b E s : ℝ) (τ m : Fin np → ℝ) (Q : Measure Ω)
    (tseq : Ω → ℕ → ℝ) (G : ℝ≥0 → Ω → GramState (SrcCol K (Fin np)))
    (Kc : ℝ≥0 → Ω → Matrix (Fin np) (Fin np) ℂ) (σ : ℝ → Ω → WithTop ℝ≥0) : Prop where
  drift : ∀ (L : ℝ) (e : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np)),
    IsTestedMart Q (complexObs tseq G Kc)
      (stoppedProcess (cComp b E s τ m G Kc (Sum.inl e)) (σ L))
  bracket : ∀ (L : ℝ) (e e' : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np)),
    IsTestedMart Q (complexObs tseq G Kc)
      (stoppedProcess (cBr b E s τ m G Kc (Sum.inl e) (Sum.inl e')) (σ L))

/-- **The `𝒦`-involving coordinate identities** stopped at the family of stops `σ L`: the drift
of a `𝒦` entry, its bilinear brackets with `𝒦` and Gram entries, and the conjugate bracket of
two `𝒦` entries. -/
structure IsKCoordTested [MeasurableSpace Ω] (b E s : ℝ) (τ m : Fin np → ℝ) (Q : Measure Ω)
    (tseq : Ω → ℕ → ℝ) (G : ℝ≥0 → Ω → GramState (SrcCol K (Fin np)))
    (Kc : ℝ≥0 → Ω → Matrix (Fin np) (Fin np) ℂ) (σ : ℝ → Ω → WithTop ℝ≥0) : Prop where
  drift : ∀ (L : ℝ) (ij : Fin np × Fin np), IsTestedMart Q (complexObs tseq G Kc)
    (stoppedProcess (cComp b E s τ m G Kc (Sum.inr ij)) (σ L))
  bracketK : ∀ (L : ℝ) (ij kl : Fin np × Fin np), IsTestedMart Q (complexObs tseq G Kc)
    (stoppedProcess (cBr b E s τ m G Kc (Sum.inr ij) (Sum.inr kl)) (σ L))
  bracketG : ∀ (L : ℝ) (ij : Fin np × Fin np) (e : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np)),
    IsTestedMart Q (complexObs tseq G Kc)
      (stoppedProcess (cBr b E s τ m G Kc (Sum.inr ij) (Sum.inl e)) (σ L))
  conjBr : ∀ (L : ℝ) (ij kl : Fin np × Fin np), IsTestedMart Q (complexObs tseq G Kc)
    (stoppedProcess (kBr b E s τ m G Kc ij kl) (σ L))

/-- **The seven clauses from the coordinate identities**: with the data fields, the Gram and
`𝒦` coordinate identities at the Gram trace stops give `IsStoppedTestedComplexModel`. -/
theorem isStoppedTestedComplexModel_of_coord [MeasurableSpace Ω] {h : ℝ}
    {entrance : Measure (Measure unitInterval)} {Q : Measure Ω} {tseq : Ω → ℕ → ℝ}
    (hQ : IsProbabilityMeasure Q) (htm : Measurable tseq) (hGm : ∀ u, StronglyMeasurable (G u))
    (hKm : ∀ u, StronglyMeasurable (Kc u)) (hseq : ∀ᵐ ω ∂Q, IsTransmissionSequence (tseq ω))
    (hlaw : Q.map (fun ω => seqTraceMeasure (tseq ω)) = entrance)
    (hinit : ∀ᵐ ω ∂Q, G 0 ω = initialGram K (Fin np) (tseq ω) h ∧ Kc 0 ω = 0)
    (hc : ∀ ω, Continuous fun u => G u ω - gramJ b s τ m u)
    (hkc : ∀ ω, Continuous fun u => Kc u ω - kJ E s τ m u)
    (hfeas : ∀ᵐ ω ∂Q, ∀ t, GramFeasible (srcSignature K (Fin np)) (G t ω))
    (hGr : IsGramCoordTested b E s τ m Q tseq G Kc (gramTraceStop G))
    (hKr : IsKCoordTested b E s τ m Q tseq G Kc (gramTraceStop G)) :
    IsStoppedTestedComplexModel b E s τ m h K entrance Q tseq G Kc where
  prob := hQ
  entrance_measurable := htm
  gram_measurable := hGm
  k_measurable := hKm
  entrance_sequence := hseq
  entrance_law := hlaw
  initial := hinit
  continuous := hc
  k_continuous := hkc
  feasible := hfeas
  drift L e := hGr.drift L e
  bracket L e e' := by rw [bracket_eq_cBr]; exact hGr.bracket L e e'
  martingale L i j := by
    have := hKr.drift L (i, j)
    rwa [cComp_inr] at this
  holomorphic L i j k l := by rw [holo_eq_cBr]; exact hKr.bracketK L (i, j) (k, l)
  antiholomorphic L i j k l := by rw [antiholo_eq_kBr]; exact hKr.conjBr L (i, j) (k, l)
  crossM L i j k l := by rw [crossM_eq_cBr]; exact hKr.bracketG L (i, j) (0, k, l)
  crossB L i j k l := by rw [crossB_eq_cBr]; exact hKr.bracketG L (i, j) (1, k, l)

end BlockBand.SourceProcess.PhysApprox.B3.Ident2
