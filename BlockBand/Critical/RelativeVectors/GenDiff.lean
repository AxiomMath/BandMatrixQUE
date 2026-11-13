module

public import BlockBand.Critical.RelativeVectors.AngularFields

/-!
# The exact generator difference

For any `h : (ℂ^r)^N → ℝ`, with `D¹ = Dh(z)`, `D² = D(Dh)(z)` (real derivatives, no symmetry and
no differentiability needed: the identity is linear algebra in `D¹, D²`), the eigenvalues
`λ = λ(H_σ)` of the flow, couplings `c_ij = 1/(N(λ_i-λ_j)²)`, `β_i = Σ_{|i-j| ≥ ℓ} c_ij`
(`longCoupling`), `β̂_i = max(β_i, b₀N/ℓ)` (`refDamping`), and `ℓ ≥ 1`:

`𝒜h - 𝓛_ref h = diagError + crossError + floorError` (`generator_diff_eq`), where
* `hq D² i v = D²(e_i v, e_i v) + D²(e_i iv, e_i iv)` (the Hermitian Hessian form of label `i`
  in the direction `v ∈ ℂ^r`; `e_i v = Pi.single i v`);
* `diagError = ¼ Σ_i Σ_{|i-j| ≥ ℓ} c_ij (hq D² i z_j - Σ_q hq D² i e_q)`: one quarter of the
  contraction of the label-`i` real Hessian with `Δ_i = Σ_{|i-j|≥ℓ} c_ij(z_jz_j^* - I_r)`;
* `crossError = ¼ Σ_{i<j, |i-j| ≥ ℓ} c_ij crossTerm`, `crossTerm = D²(e_i iz_j, e_j iz_i) +
  D²(e_j iz_i, e_i iz_j) - D²(e_i z_j, e_j z_i) - D²(e_j z_i, e_i z_j)` (for symmetric `D²` this is
  `(c_ij/2){D²_ij g[iz_j, iz_i] - D²_ij g[z_j, z_i]}`);
* `floorError = Σ_i (β̂_i - β_i)(½ D¹(e_i z_i) - ¼ Σ_q hq D² i e_q)` (the Ornstein–Uhlenbeck floor
  error).

Also: `complexAngularGenerator_split` (short + long rotations) and
`referenceArrayGenerator_eq` (the short rotations of the reference generator are those of the
true generator, so they cancel exactly).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open Finset Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission

variable {N r : ℕ}

/-- Real bilinear forms on arrays (second derivatives). -/
abbrev ArrBil (N r : ℕ) :=
  (Fin N → Fin r → ℂ) →L[ℝ] (Fin N → Fin r → ℂ) →L[ℝ] ℝ

/-- The array `e_i v`: `v` at label `i`, zero elsewhere. -/
abbrev single (i : Fin N) (v : Fin r → ℂ) : Fin N → Fin r → ℂ := Pi.single i v

/-- Hermitian Hessian form of label `i` in direction `v`: `D²(e_i v, e_i v) + D²(e_i iv, e_i iv)`. -/
def hq (D2 : ArrBil N r) (i : Fin N) (v : Fin r → ℂ) : ℝ :=
  D2 (single i v) (single i v) + D2 (single i (Complex.I • v)) (single i (Complex.I • v))

/-- Trace of the label-`i` Hermitian Hessian form: `Σ_q hq D² i e_q`. -/
def hqTrace (D2 : ArrBil N r) (i : Fin N) : ℝ := ∑ q : Fin r, hq D2 i (Pi.single q 1)

/-- Cross term of the pair `(i, j)`. -/
def crossTerm (D2 : ArrBil N r) (z : Fin N → Fin r → ℂ) (i j : Fin N) : ℝ :=
  D2 (single i (Complex.I • z j)) (single j (Complex.I • z i)) +
    D2 (single j (Complex.I • z i)) (single i (Complex.I • z j)) -
    D2 (single i (z j)) (single j (z i)) - D2 (single j (z i)) (single i (z j))

/-- Diagonal covariance error `¼ Σ_i Σ_{|i-j| ≥ ℓ} c_ij (hq_i(z_j) - Σ_q hq_i(e_q))`. -/
def diagError (N r : ℕ) (lam : Fin N → ℝ) (ℓ : ℕ) (D2 : ArrBil N r)
    (z : Fin N → Fin r → ℂ) : ℝ :=
  (1 / 4 : ℝ) * ∑ i, ∑ j ∈ univ.filter (fun j => ℓ ≤ labelDist i j),
    dysonCoupling N lam i j * (hq D2 i (z j) - hqTrace D2 i)

/-- Cross-Hessian error `¼ Σ_{i<j, |i-j| ≥ ℓ} c_ij crossTerm_ij`. -/
def crossError (N r : ℕ) (lam : Fin N → ℝ) (ℓ : ℕ) (D2 : ArrBil N r)
    (z : Fin N → Fin r → ℂ) : ℝ :=
  (1 / 4 : ℝ) * ∑ i, ∑ j ∈ univ.filter (fun j => i < j ∧ ℓ ≤ labelDist i j),
    dysonCoupling N lam i j * crossTerm D2 z i j

/-- Ornstein–Uhlenbeck floor error `Σ_i (β̂_i - β_i)(½ D¹(e_i z_i) - ¼ Σ_q hq_i(e_q))`. -/
def floorError (bh b : Fin N → ℝ) (D1 : (Fin N → Fin r → ℂ) →L[ℝ] ℝ) (D2 : ArrBil N r)
    (z : Fin N → Fin r → ℂ) : ℝ :=
  ∑ i, (bh i - b i) * ((1 / 2 : ℝ) * D1 (single i (z i)) -
    (1 / 4 : ℝ) * hqTrace D2 i)

/-- Rotations restricted by a label-distance predicate: `¼ Σ_{i<j, P} c_ij (X²+Y²)h`. -/
def rotPart (N r : ℕ) (lam : Fin N → ℝ) (P : Fin N → Fin N → Prop) [DecidableRel P]
    (h : (Fin N → Fin r → ℂ) → ℝ) (z : Fin N → Fin r → ℂ) : ℝ :=
  (1 / 4 : ℝ) * ∑ i, ∑ j ∈ univ.filter (fun j => i < j ∧ P i j),
    dysonCoupling N lam i j * (fieldSq (rotX i j) h z + fieldSq (rotY i j) h z)

/-!
## Elementary facts
-/

theorem dysonCoupling_symm (lam : Fin N → ℝ) (i j : Fin N) :
    dysonCoupling N lam i j = dysonCoupling N lam j i := by
  unfold dysonCoupling; ring

theorem dysonCoupling_flow (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ω : FlowSample N) (σ : ℝ)
    (i j : Fin N) : dysonCoupling N (flowEigenvalue F a ω σ) i j = flowRate F a ω σ i j := by
  unfold dysonCoupling flowRate; rw [one_div]

theorem labelDist_symm (i j : Fin N) : labelDist i j = labelDist j i := by
  unfold labelDist; omega

theorem labelDist_self (i : Fin N) : labelDist i i = 0 := by simp [labelDist]

theorem rotX_eq {i j : Fin N} (hij : i ≠ j) (z : Fin N → Fin r → ℂ) :
    rotX i j z = single i (z j) - single j (z i) := by
  funext k
  by_cases hki : k = i
  · subst hki; simp [rotX, single, hij]
  · by_cases hkj : k = j
    · subst hkj; simp [rotX, single, hki]
    · simp [rotX, single, hki, hkj]

theorem rotY_eq {i j : Fin N} (hij : i ≠ j) (z : Fin N → Fin r → ℂ) :
    rotY i j z = single i (Complex.I • z j) + single j (Complex.I • z i) := by
  funext k
  by_cases hki : k = i
  · subst hki; simp [rotY, single, hij]
  · by_cases hkj : k = j
    · subst hkj; simp [rotY, single, hki]
    · simp [rotY, single, hki, hkj]

theorem rotX_rotX {i j : Fin N} (hij : i ≠ j) (z : Fin N → Fin r → ℂ) :
    rotX i j (rotX i j z) = -(single i (z i) + single j (z j)) := by
  funext k
  have hji : j ≠ i := Ne.symm hij
  by_cases hki : k = i
  · subst hki; simp [rotX, single, hij, hji]
  · by_cases hkj : k = j
    · subst hkj; simp [rotX, single, hki]
    · simp [rotX, single, hki, hkj]

theorem rotY_rotY {i j : Fin N} (hij : i ≠ j) (z : Fin N → Fin r → ℂ) :
    rotY i j (rotY i j z) = -(single i (z i) + single j (z j)) := by
  funext k
  have hji : j ≠ i := Ne.symm hij
  have hII : ∀ v : Fin r → ℂ, Complex.I • Complex.I • v = -v := by
    intro v; rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  by_cases hki : k = i
  · subst hki; simp [rotY, single, hij, hji, hII]
  · by_cases hkj : k = j
    · subst hkj; simp [rotY, single, hki, hII]
    · simp [rotY, single, hki, hkj]

/-- `(X_ij² + Y_ij²) h` for `i ≠ j`, expanded. -/
theorem fieldSq_rot_eq {i j : Fin N} (hij : i ≠ j) (h : (Fin N → Fin r → ℂ) → ℝ)
    (z : Fin N → Fin r → ℂ) :
    fieldSq (rotX i j) h z + fieldSq (rotY i j) h z =
      hq (fderiv ℝ (fderiv ℝ h) z) i (z j) + hq (fderiv ℝ (fderiv ℝ h) z) j (z i) +
        crossTerm (fderiv ℝ (fderiv ℝ h) z) z i j -
        2 * (fderiv ℝ h z (single i (z i)) + fderiv ℝ h z (single j (z j))) := by
  unfold fieldSq
  rw [rotX_rotX hij, rotY_rotY hij, rotX_eq hij, rotY_eq hij]
  simp only [hq, crossTerm, map_sub, map_add, map_neg, _root_.sub_apply,
    _root_.add_apply]
  ring

/-!
## Sums over pairs
-/

/-- `Σ_{i<j, P} (u_ij + u_ji) = Σ_{i ≠ j, P} u_ij` for a symmetric predicate `P`. -/
theorem sum_pairs_symm (P : Fin N → Fin N → Prop) [DecidableRel P]
    (hP : ∀ i j, P i j → P j i) (u : Fin N → Fin N → ℝ) :
    ∑ i, ∑ j ∈ univ.filter (fun j => i < j ∧ P i j), (u i j + u j i) =
      ∑ i, ∑ j ∈ univ.filter (fun j => i ≠ j ∧ P i j), u i j := by
  simp only [Finset.sum_filter, Finset.sum_add_distrib]
  have hswap : ∑ i, ∑ j, (if i < j ∧ P i j then u j i else 0) =
      ∑ i, ∑ j, (if j < i ∧ P i j then u i j else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases h1 : j < i
    · by_cases h2 : P i j
      · simp [h1, h2, hP i j h2]
      · have : ¬ P j i := fun h => h2 (hP j i h)
        simp [h2, this]
    · simp [h1]
  have hsplit : ∀ i j : Fin N, (if i < j ∧ P i j then u i j else 0) +
      (if j < i ∧ P i j then u i j else 0) = (if i ≠ j ∧ P i j then u i j else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · subst h; simp
    · simp [h, h.ne', not_lt.mpr h.le]
  rw [hswap, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => hsplit i j

/-!
## The split of the true generator and the short part of the reference generator
-/

theorem complexAngularGenerator_split (lam : Fin N → ℝ) (ℓ : ℕ)
    (h : (Fin N → Fin r → ℂ) → ℝ) (z : Fin N → Fin r → ℂ) :
    complexAngularGenerator N r lam h z =
      rotPart N r lam (fun i j => labelDist i j < ℓ) h z +
        rotPart N r lam (fun i j => ℓ ≤ labelDist i j) h z := by
  unfold complexAngularGenerator rotPart
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_filter_add_sum_filter_not (univ.filter fun j => i < j)
    (fun j => labelDist i j < ℓ)]
  simp only [Finset.filter_filter, not_lt]

/-- The reference generator is the short rotations of the true flow plus the OU part. -/
theorem referenceArrayGenerator_eq (F : Matrix (Fin N) (Fin N) ℂ) (a b₀ : ℝ) (ω : FlowSample N)
    (ℓ : ℕ) (σ : ℝ) (h : (Fin N → Fin r → ℂ) → ℝ) (z : Fin N → Fin r → ℂ) :
    referenceArrayGenerator F a b₀ ω ℓ σ h z =
      rotPart N r (flowEigenvalue F a ω σ) (fun i j => labelDist i j < ℓ) h z +
        ∑ i, refDamping F a b₀ ω ℓ σ i *
          (-(1 / 2 : ℝ) * fderiv ℝ h z (single i (z i)) +
            (1 / 4 : ℝ) * hqTrace (fderiv ℝ (fderiv ℝ h) z) i) := by
  unfold referenceArrayGenerator rotPart
  have hI : ∀ q : Fin r, Complex.I • (Pi.single q (1 : ℂ) : Fin r → ℂ) = Pi.single q Complex.I := by
    intro q; funext q'; by_cases hq' : q' = q
    · subst hq'; simp
    · simp [hq']
  simp only [hqTrace, hq, hI, dysonCoupling_flow]

/-- `β_i = Σ_{|i-j| ≥ ℓ} c_ij`. -/
theorem longCoupling_eq (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ω : FlowSample N) (ℓ : ℕ)
    (hℓ : 1 ≤ ℓ) (σ : ℝ) (i : Fin N) :
    longCoupling F a ω ℓ σ i = ∑ j ∈ univ.filter (fun j => i ≠ j ∧ ℓ ≤ labelDist i j),
      dysonCoupling N (flowEigenvalue F a ω σ) i j := by
  unfold longCoupling
  refine Finset.sum_congr ?_ fun j _ => (dysonCoupling_flow F a ω σ i j).symm
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hj
    refine ⟨fun hij => ?_, hj⟩
    subst hij
    rw [labelDist_self] at hj
    omega
  · exact fun h => h.2

/-!
## The generator difference
-/

/-- The long (or any symmetric) rotations, expanded with symmetric couplings. -/
theorem rotPart_expand (lam : Fin N → ℝ) (P : Fin N → Fin N → Prop) [DecidableRel P]
    (hP : ∀ i j, P i j → P j i) (h : (Fin N → Fin r → ℂ) → ℝ) (z : Fin N → Fin r → ℂ) :
    rotPart N r lam P h z =
      (1 / 4 : ℝ) * ∑ i, ∑ j ∈ univ.filter (fun j => i ≠ j ∧ P i j),
          dysonCoupling N lam i j * hq (fderiv ℝ (fderiv ℝ h) z) i (z j) +
        (1 / 4 : ℝ) * ∑ i, ∑ j ∈ univ.filter (fun j => i < j ∧ P i j),
          dysonCoupling N lam i j * crossTerm (fderiv ℝ (fderiv ℝ h) z) z i j -
        (1 / 2 : ℝ) * ∑ i, ∑ j ∈ univ.filter (fun j => i ≠ j ∧ P i j),
          dysonCoupling N lam i j * fderiv ℝ h z (single i (z i)) := by
  unfold rotPart
  have e1 : ∀ i, ∑ j ∈ univ.filter (fun j => i < j ∧ P i j),
      dysonCoupling N lam i j * (fieldSq (rotX i j) h z + fieldSq (rotY i j) h z) =
      ∑ j ∈ univ.filter (fun j => i < j ∧ P i j),
        ((dysonCoupling N lam i j * hq (fderiv ℝ (fderiv ℝ h) z) i (z j) +
            dysonCoupling N lam j i * hq (fderiv ℝ (fderiv ℝ h) z) j (z i)) +
          dysonCoupling N lam i j * crossTerm (fderiv ℝ (fderiv ℝ h) z) z i j -
          2 * (dysonCoupling N lam i j * fderiv ℝ h z (single i (z i)) +
            dysonCoupling N lam j i * fderiv ℝ h z (single j (z j)))) := by
    intro i
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [fieldSq_rot_eq (Finset.mem_filter.mp hj).2.1.ne, dysonCoupling_symm lam j i]
    ring
  simp_rw [e1]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have s1 := sum_pairs_symm P hP (fun i j => dysonCoupling N lam i j *
    hq (fderiv ℝ (fderiv ℝ h) z) i (z j))
  have s2 := sum_pairs_symm P hP (fun i j => dysonCoupling N lam i j *
    fderiv ℝ h z (single i (z i)))
  simp only [Finset.sum_add_distrib] at s1 s2
  rw [s1, s2]
  ring

/-- **The exact generator difference.** See the module docstring. -/
theorem generator_diff_eq (F : Matrix (Fin N) (Fin N) ℂ) (a b₀ : ℝ) (ω : FlowSample N)
    {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (σ : ℝ) (h : (Fin N → Fin r → ℂ) → ℝ) (z : Fin N → Fin r → ℂ) :
    complexAngularGenerator N r (flowEigenvalue F a ω σ) h z -
        referenceArrayGenerator F a b₀ ω ℓ σ h z =
      diagError N r (flowEigenvalue F a ω σ) ℓ (fderiv ℝ (fderiv ℝ h) z) z +
        crossError N r (flowEigenvalue F a ω σ) ℓ (fderiv ℝ (fderiv ℝ h) z) z +
        floorError (refDamping F a b₀ ω ℓ σ) (longCoupling F a ω ℓ σ) (fderiv ℝ h z)
          (fderiv ℝ (fderiv ℝ h) z) z := by
  rw [complexAngularGenerator_split _ ℓ, referenceArrayGenerator_eq,
    rotPart_expand _ (fun i j => ℓ ≤ labelDist i j) (fun i j hij => by rwa [labelDist_symm])]
  have hfilt : ∀ i : Fin N, univ.filter (fun j => i ≠ j ∧ ℓ ≤ labelDist i j) =
      univ.filter (fun j => ℓ ≤ labelDist i j) := by
    intro i; ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro hj
      refine ⟨fun hij => ?_, hj⟩
      subst hij; rw [labelDist_self] at hj; omega
  have hb : ∀ i, longCoupling F a ω ℓ σ i =
      ∑ j ∈ univ.filter (fun j => ℓ ≤ labelDist i j), dysonCoupling N (flowEigenvalue F a ω σ) i j := by
    intro i; rw [longCoupling_eq F a ω ℓ hℓ σ i, hfilt]
  simp only [hfilt]
  set lam := flowEigenvalue F a ω σ
  set D1 := fderiv ℝ h z
  set D2 := fderiv ℝ (fderiv ℝ h) z
  set β := longCoupling F a ω ℓ σ
  set bh := refDamping F a b₀ ω ℓ σ
  have hdiag : diagError N r lam ℓ D2 z =
      (1 / 4 : ℝ) * ∑ i, ∑ j ∈ univ.filter (fun j => ℓ ≤ labelDist i j),
        dysonCoupling N lam i j * hq D2 i (z j) - (1 / 4 : ℝ) * ∑ i, β i * hqTrace D2 i := by
    unfold diagError
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hb i, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hfloor : floorError bh β D1 D2 z =
      (1 / 2 : ℝ) * ∑ i, bh i * D1 (single i (z i)) - (1 / 2 : ℝ) * ∑ i, β i * D1 (single i (z i)) -
        (1 / 4 : ℝ) * ∑ i, bh i * hqTrace D2 i + (1 / 4 : ℝ) * ∑ i, β i * hqTrace D2 i := by
    unfold floorError
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hC : ∑ i, ∑ j ∈ univ.filter (fun j => ℓ ≤ labelDist i j),
      dysonCoupling N lam i j * D1 (single i (z i)) = ∑ i, β i * D1 (single i (z i)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hb i, Finset.sum_mul]
  have hOU : ∑ i, bh i * (-(1 / 2 : ℝ) * D1 (single i (z i)) + (1 / 4 : ℝ) * hqTrace D2 i) =
      -(1 / 2 : ℝ) * ∑ i, bh i * D1 (single i (z i)) + (1 / 4 : ℝ) * ∑ i, bh i * hqTrace D2 i := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hdiag, hfloor, hC, hOU]
  unfold crossError
  ring

end BlockBand.Critical.RelativeVectors
