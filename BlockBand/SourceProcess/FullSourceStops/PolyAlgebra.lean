module

public import BlockBand.Internal.Contracts.TransmissionStatements

/-!
# The contraction rule produces ordinary words, linearly in `D₀`

* `ordPoly`: the subalgebra of polynomials in ordinary words (`MvPolynomial.supported`);
  `pderiv_mem_supported`: partial derivatives stay in it.
* `wordDrift_mem`, `wordCov_mem`: for ordinary `w, v` every word produced by `pairTerm` and
  `crossTerm` is ordinary (nonempty, separators `I`, `P`).
* `wordDrift_eq`, `wordCov_eq`: `wordDrift D₀ w = D₀ · wordDrift 1 w`, same for `wordCov`.
* `wordGenerator_eq`, `wordCarre_eq`: `𝒜_tΦ = D₀ · genCore Φ + Σ_w inj_w(t) ∂_wΦ` and
  `Γ(Φ) = D₀ · carreCore Φ` with `genCore`, `carreCore` independent of `E` and `t`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceStops

open MvPolynomial
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionPath

variable {nT nI : ℕ}

/-- Polynomials in ordinary words. -/
abbrev ordPoly (nT nI : ℕ) : Subalgebra ℂ (TracePoly nT nI) :=
  supported ℂ {w : TraceWord nT nI | IsOrdinaryWord w}

theorem pderiv_mem_supported {σ : Type*} {s : Set σ} {p : MvPolynomial σ ℂ}
    (hp : p ∈ supported ℂ s) (i : σ) : pderiv i p ∈ supported ℂ s := by
  classical
  rw [supported_eq_adjoin_X] at hp ⊢
  induction hp using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, -, rfl⟩ := hx
    rw [pderiv_X, Pi.single_apply]
    split_ifs
    · exact Subalgebra.one_mem _
    · exact Subalgebra.zero_mem _
  | algebraMap r => rw [Derivation.map_algebraMap]; exact Subalgebra.zero_mem _
  | add x y _ _ ihx ihy => rw [map_add]; exact Subalgebra.add_mem _ ihx ihy
  | mul x y hx hy ihx ihy =>
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ hx ihy) (Subalgebra.mul_mem _ hy ihx)

theorem C_mem_ordPoly (c : ℂ) : (C c : TracePoly nT nI) ∈ ordPoly nT nI :=
  Subalgebra.algebraMap_mem _ c

theorem wv_mem_ordPoly {w : TraceWord nT nI} (hw : IsOrdinaryWord w) : wv w ∈ ordPoly nT nI :=
  (X_mem_supported (R := ℂ)).mpr hw

theorem mem_ordPoly_of_isOrdinaryPoly {Φ : TracePoly nT nI} (hΦ : IsOrdinaryPoly Φ) :
    Φ ∈ ordPoly nT nI :=
  mem_supported.mpr fun w hw => hΦ w hw

/-!
## Words produced by the contraction rule
-/

/-- Separators `I` or `P` only. -/
def SepGood (w : TraceWord nT nI) : Prop := ∀ x ∈ w, x.2 = .id ∨ x.2 = .proj

theorem sepGood_rotate {w : TraceWord nT nI} (h : SepGood w) (n : ℕ) : SepGood (w.rotate n) :=
  fun x hx => h x (List.mem_rotate.mp hx)

theorem sepGood_take {w : TraceWord nT nI} (h : SepGood w) (n : ℕ) : SepGood (w.take n) :=
  fun x hx => h x (List.mem_of_mem_take hx)

theorem sepGood_append {u v : TraceWord nT nI} (hu : SepGood u) (hv : SepGood v) :
    SepGood (u ++ v) := fun x hx => (List.mem_append.mp hx).elim (hu x) (hv x)

theorem sepGood_setLastSep {w : TraceWord nT nI} (h : SepGood w) :
    SepGood (setLastSep w .proj) := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact h x (List.dropLast_subset _ hx)
  · rw [Option.mem_toList] at hx
    obtain ⟨y, -, rfl⟩ := Option.map_eq_some_iff.mp hx
    exact Or.inr rfl

theorem setLastSep_ne_nil {w : TraceWord nT nI} (h : w ≠ []) (s : Separator) :
    setLastSep w s ≠ [] := by
  rw [setLastSep, List.getLast?_eq_some_getLast h]
  simp

theorem sepAt_good {w : TraceWord nT nI} (h : SepGood w) (i : ℕ) :
    sepAt w i = .id ∨ sepAt w i = .proj := by
  rw [sepAt, List.getD_eq_getElem?_getD]
  rcases hw : w[i]? with _ | x
  · exact Or.inl rfl
  · exact h x (List.mem_of_getElem? hw)

theorem sepGood_current {s : Separator} (hs : s = .id ∨ s = .proj) :
    SepGood ([(.current, s)] : TraceWord nT nI) := by
  intro x hx; rw [List.mem_singleton] at hx; subst hx; exact hs

theorem ord_setLastSep {w : TraceWord nT nI} (h : SepGood w) (hne : w ≠ []) :
    IsOrdinaryWord (setLastSep w .proj) :=
  ⟨setLastSep_ne_nil hne _, sepGood_setLastSep h⟩

theorem ord_append_current {w u : TraceWord nT nI} (h : SepGood w) (hu : SepGood u)
    (hne : w ≠ []) {s : Separator} (hs : s = .id ∨ s = .proj) :
    IsOrdinaryWord (w ++ [(.current, s)] ++ u) :=
  ⟨by simp [hne], sepGood_append (sepGood_append h (sepGood_current hs)) hu⟩

theorem ord_snoc_current {w : TraceWord nT nI} (h : SepGood w) {s : Separator}
    (hs : s = .id ∨ s = .proj) : IsOrdinaryWord (w ++ [(.current, s)]) :=
  ⟨by simp, sepGood_append h (sepGood_current hs)⟩

theorem pairTerm_mem (D0 : ℝ) {w : TraceWord nT nI} (hw : IsOrdinaryWord w) {i j : ℕ}
    (hij : i < j) (hj : j < w.length) : pairTerm D0 w i j ∈ ordPoly nT nI := by
  have hg := hw.2
  have hne : w ≠ [] := hw.1
  have h1 : SepGood ((w.rotate (j + 1)).take (w.length - (j - i))) :=
    sepGood_take (sepGood_rotate hg _) _
  have h2 : SepGood ((w.rotate (i + 1)).take (j - i)) := sepGood_take (sepGood_rotate hg _) _
  have n1 : (w.rotate (j + 1)).take (w.length - (j - i)) ≠ [] := by
    rw [Ne, List.take_eq_nil_iff, List.rotate_eq_nil_iff]; exact not_or.mpr ⟨by omega, hne⟩
  have n2 : (w.rotate (i + 1)).take (j - i) ≠ [] := by
    rw [Ne, List.take_eq_nil_iff, List.rotate_eq_nil_iff]; exact not_or.mpr ⟨by omega, hne⟩
  have hAP := wv_mem_ordPoly (ord_setLastSep h1 n1)
  have hBP := wv_mem_ordPoly (ord_setLastSep h2 n2)
  have hAJ := wv_mem_ordPoly (ord_snoc_current h1 (sepAt_good hg j))
  have hBJ := wv_mem_ordPoly (ord_snoc_current h2 (sepAt_good hg i))
  unfold pairTerm
  exact Subalgebra.mul_mem _ (C_mem_ordPoly _) (Subalgebra.add_mem _
    (Subalgebra.mul_mem _ hAP (Subalgebra.add_mem _ hBP hBJ))
    (Subalgebra.mul_mem _ (Subalgebra.add_mem _ hAP hAJ) hBP))

theorem crossTerm_mem (D0 : ℝ) {w v : TraceWord nT nI} (hw : IsOrdinaryWord w)
    (hv : IsOrdinaryWord v) (i j : ℕ) : crossTerm D0 w v i j ∈ ordPoly nT nI := by
  have gw := sepGood_rotate hw.2 (i + 1)
  have gv := sepGood_rotate hv.2 (j + 1)
  have nw : w.rotate (i + 1) ≠ [] := by rw [Ne, List.rotate_eq_nil_iff]; exact hw.1
  have nv : v.rotate (j + 1) ≠ [] := by rw [Ne, List.rotate_eq_nil_iff]; exact hv.1
  have hbase := wv_mem_ordPoly (nT := nT) (nI := nI)
    (w := setLastSep (w.rotate (i + 1)) .proj ++ setLastSep (v.rotate (j + 1)) .proj)
    ⟨by simp [setLastSep_ne_nil nw], sepGood_append (sepGood_setLastSep gw) (sepGood_setLastSep gv)⟩
  have h1 := wv_mem_ordPoly
    (ord_snoc_current (sepGood_append (sepGood_setLastSep gw) gv) (sepAt_good hw.2 i))
  have h2 := wv_mem_ordPoly (ord_append_current gw (sepGood_setLastSep gv) nw (sepAt_good hv.2 j))
  unfold crossTerm
  exact Subalgebra.mul_mem _ (C_mem_ordPoly _)
    (Subalgebra.add_mem _ (Subalgebra.add_mem _ hbase h1) (Subalgebra.add_mem _ hbase h2))

theorem wordDrift_mem (D0 : ℝ) {w : TraceWord nT nI} (hw : IsOrdinaryWord w) :
    wordDrift D0 w ∈ ordPoly nT nI := by
  have hg : (gPoly : TracePoly nT nI) ∈ ordPoly nT nI :=
    Subalgebra.mul_mem _ (C_mem_ordPoly _) (wv_mem_ordPoly ⟨by simp, by
      intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> exact Or.inl rfl⟩)
  unfold wordDrift
  refine Subalgebra.add_mem _ (Subalgebra.neg_mem _ (Subalgebra.mul_mem _ (Subalgebra.mul_mem _
    (Subalgebra.mul_mem _ (C_mem_ordPoly _) hg) (C_mem_ordPoly _)) (wv_mem_ordPoly hw))) ?_
  refine Subalgebra.sum_mem _ fun i _ => Subalgebra.sum_mem _ fun j hj => ?_
  obtain ⟨hij, hjl⟩ := Finset.mem_Ioo.mp hj
  exact pairTerm_mem D0 hw hij hjl

theorem wordCov_mem (D0 : ℝ) {w v : TraceWord nT nI} (hw : IsOrdinaryWord w)
    (hv : IsOrdinaryWord v) : wordCov D0 w v ∈ ordPoly nT nI :=
  Subalgebra.sum_mem _ fun i _ => Subalgebra.sum_mem _ fun j _ => crossTerm_mem D0 hw hv i j

/-!
## Linearity in `D₀`
-/

theorem C_half (D0 : ℝ) :
    (C ((D0 / 2 : ℝ) : ℂ) : TracePoly nT nI) = C (D0 : ℂ) * C ((1 / 2 : ℝ) : ℂ) := by
  rw [← map_mul]; congr 1; push_cast; ring

theorem pairTerm_eq (D0 : ℝ) (w : TraceWord nT nI) (i j : ℕ) :
    pairTerm D0 w i j = C (D0 : ℂ) * pairTerm 1 w i j := by
  unfold pairTerm; rw [C_half D0, C_half (nT := nT) (nI := nI) 1]; push_cast; ring

theorem crossTerm_eq (D0 : ℝ) (w v : TraceWord nT nI) (i j : ℕ) :
    crossTerm D0 w v i j = C (D0 : ℂ) * crossTerm 1 w v i j := by
  unfold crossTerm; rw [C_half D0, C_half (nT := nT) (nI := nI) 1]; push_cast; ring

theorem wordDrift_eq (D0 : ℝ) (w : TraceWord nT nI) :
    wordDrift D0 w = C (D0 : ℂ) * wordDrift 1 w := by
  unfold wordDrift
  simp only [pairTerm_eq D0 w, ← Finset.mul_sum]
  rw [C_half D0, C_half (nT := nT) (nI := nI) 1]; push_cast; ring

theorem wordCov_eq (D0 : ℝ) (w v : TraceWord nT nI) :
    wordCov D0 w v = C (D0 : ℂ) * wordCov 1 w v := by
  unfold wordCov; simp only [crossTerm_eq D0 w v, ← Finset.mul_sum]

/-- The `E`- and `t`-free part of the generator. -/
def genCore (Φ : TracePoly nT nI) : TracePoly nT nI :=
  ∑ w ∈ Φ.vars, pderiv w Φ * wordDrift 1 w +
    C (1 / 2 : ℂ) * ∑ w ∈ Φ.vars, ∑ v ∈ Φ.vars, pderiv v (pderiv w Φ) * wordCov 1 w v

/-- The `E`-free part of the bracket rate. -/
def carreCore (Φ : TracePoly nT nI) : TracePoly nT nI :=
  ∑ w ∈ Φ.vars, ∑ v ∈ Φ.vars, pderiv w Φ * pderiv v Φ * wordCov 1 w v

theorem wordGenerator_eq (b E : ℝ) (q : Fin nI → ℝ → ℝ) (t : ℝ) (Φ : TracePoly nT nI) :
    wordGenerator b E q t Φ = C ((transportD0 b E : ℝ) : ℂ) * genCore Φ +
      ∑ w ∈ Φ.vars, C (wordInjection b q t w) * pderiv w Φ := by
  unfold wordGenerator genCore
  simp only [wordDrift_eq (transportD0 b E), wordCov_eq (transportD0 b E), mul_add,
    Finset.sum_add_distrib, Finset.mul_sum]
  have e1 : ∀ w ∈ Φ.vars, pderiv w Φ * (C ((transportD0 b E : ℝ) : ℂ) * wordDrift 1 w) =
      C ((transportD0 b E : ℝ) : ℂ) * (pderiv w Φ * wordDrift 1 w) := fun _ _ => by ring
  have e2 : ∀ w ∈ Φ.vars, ∀ v ∈ Φ.vars, C (1 / 2 : ℂ) * (pderiv v (pderiv w Φ) *
      (C ((transportD0 b E : ℝ) : ℂ) * wordCov 1 w v)) = C ((transportD0 b E : ℝ) : ℂ) *
        (C (1 / 2 : ℂ) * (pderiv v (pderiv w Φ) * wordCov 1 w v)) := fun _ _ _ _ => by ring
  have e3 : ∀ w ∈ Φ.vars, pderiv w Φ * C (wordInjection b q t w) =
      C (wordInjection b q t w) * pderiv w Φ := fun _ _ => by ring
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl fun w hw => Finset.sum_congr rfl (e2 w hw),
    Finset.sum_congr rfl e3]
  abel

theorem wordCarre_eq (b E : ℝ) (Φ : TracePoly nT nI) :
    wordCarre b E Φ = C ((transportD0 b E : ℝ) : ℂ) * carreCore Φ := by
  unfold wordCarre carreCore
  simp only [wordCov_eq (transportD0 b E), Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem genCore_mem {Φ : TracePoly nT nI} (hΦ : IsOrdinaryPoly Φ) : genCore Φ ∈ ordPoly nT nI := by
  have hm := mem_ordPoly_of_isOrdinaryPoly hΦ
  unfold genCore
  refine Subalgebra.add_mem _ (Subalgebra.sum_mem _ fun w hw => Subalgebra.mul_mem _
    (pderiv_mem_supported hm w) (wordDrift_mem 1 (hΦ w hw))) (Subalgebra.mul_mem _
      (C_mem_ordPoly _) (Subalgebra.sum_mem _ fun w hw => Subalgebra.sum_mem _ fun v hv =>
        Subalgebra.mul_mem _ (pderiv_mem_supported (pderiv_mem_supported hm w) v)
          (wordCov_mem 1 (hΦ w hw) (hΦ v hv))))

theorem carreCore_mem {Φ : TracePoly nT nI} (hΦ : IsOrdinaryPoly Φ) :
    carreCore Φ ∈ ordPoly nT nI := by
  have hm := mem_ordPoly_of_isOrdinaryPoly hΦ
  exact Subalgebra.sum_mem _ fun w hw => Subalgebra.sum_mem _ fun v hv =>
    Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (pderiv_mem_supported hm w)
      (pderiv_mem_supported hm v)) (wordCov_mem 1 (hΦ w hw) (hΦ v hv))

end BlockBand.SourceProcess.FullSourceStops
