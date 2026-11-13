module

public import BlockBand.Endpoints.Response.NearSchattenFiniteAlgebra
public import BlockBand.Endpoints.Response.TaggedConvexOrderWitnessStop

/-!
# The conductance and the clock on the trace stop

Part of the proof of the near-Schatten decay theorem, on a trace stop. Deterministic.

* `nsf_current_eigenvalues_abs_le_one`: the eigenvalues of `J = 𝕊*P𝕊 - P` lie in `[-1, 1]`
  (`𝕊` unitary).
* `nsf_nuclearNorm_eq`: `Tr|M| = Σ_i |λ_i|` for Hermitian `M` (`nuclearNorm`).
* `nsf_conductance_le_half_nuclearNorm`: **`g = ½ Tr J² ≤ ½ Tr|J|`**.
* `nsf_traceLoad_le_of_alive`: before the stop, at lengths `j ≥ εW`, the trace load is `≤ K`.
* `nsf_alive_bounds`: before the stop (one-source family, `q ≥ 0`, `𝕊` unitary):
  `Tr|J| ≤ K`, `g ≤ K/2`, `0 ≤ Tr A ≤ Tr Q ≤ K` and `0 ≤ λ_i ≤ Tr A`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open Matrix Finset
open scoped ComplexOrder
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.Endpoints

section Eigen

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem nsf_star_eigenvector_dot (H : Matrix n n ℂ) (hH : H.IsHermitian) (i : n) :
    star ⇑(hH.eigenvectorBasis i) ⬝ᵥ ⇑(hH.eigenvectorBasis i) = 1 := by
  rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K,
    hH.eigenvectorBasis.orthonormal.1 i]
  simp

/-- An eigenvalue of `H` is `≥ -1` when `1 + H ⪰ 0`. -/
theorem nsf_eigenvalue_ge {H : Matrix n n ℂ} (hH : H.IsHermitian) (h : (1 + H).PosSemidef)
    (i : n) : -1 ≤ hH.eigenvalues i := by
  have h1 := h.re_dotProduct_nonneg (hH.eigenvectorBasis i)
  rw [add_mulVec, one_mulVec, dotProduct_add, nsf_star_eigenvector_dot H hH i, map_add,
    ← hH.eigenvalues_eq] at h1
  simp at h1
  linarith

/-- An eigenvalue of `H` is `≤ 1` when `1 - H ⪰ 0`. -/
theorem nsf_eigenvalue_le {H : Matrix n n ℂ} (hH : H.IsHermitian) (h : (1 - H).PosSemidef)
    (i : n) : hH.eigenvalues i ≤ 1 := by
  have h1 := h.re_dotProduct_nonneg (hH.eigenvectorBasis i)
  rw [sub_mulVec, one_mulVec, dotProduct_sub, nsf_star_eigenvector_dot H hH i, map_sub,
    ← hH.eigenvalues_eq] at h1
  simp at h1
  linarith

/-- The nuclear norm of a Hermitian matrix: `Tr|M| = Σ_i |λ_i|`. -/
theorem nsf_nuclearNorm_eq {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    nuclearNorm M = ∑ i, |hM.eigenvalues i| := by
  unfold nuclearNorm
  rw [hM.roots_charpoly_eq_eigenvalues, Multiset.map_map, Finset.sum_eq_multiset_sum]
  congr 1
  refine Multiset.map_congr rfl fun i _ => ?_
  simp [Complex.norm_real]

end Eigen

variable {W : ℕ}

theorem nsf_current_isHermitian (U : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    (Uᴴ * nearProjection W * U - nearProjection W).IsHermitian :=
  (isHermitian_conjTranspose_mul_mul _ (nsf_nearProjection_isHermitian W)).sub
    (nsf_nearProjection_isHermitian W)

/-- The eigenvalues of the current `J = U*PU - P` lie in `[-1, 1]` (`U` unitary). -/
theorem nsf_current_eigenvalues_abs_le_one {U : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hU : Uᴴ * U = 1) (i : Fin 2 × Fin W) :
    |(nsf_current_isHermitian U).eigenvalues i| ≤ 1 := by
  have hP' : (Uᴴ * nearProjection W * U).PosSemidef :=
    (nsg_nearProjection_psd W).conjTranspose_mul_mul_same U
  have h1P' : (1 - Uᴴ * nearProjection W * U).PosSemidef := by
    have := (nsg_one_sub_nearProjection_psd W).conjTranspose_mul_mul_same U
    rwa [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hU] at this
  have hlo : (1 + (Uᴴ * nearProjection W * U - nearProjection W)).PosSemidef := by
    have := hP'.add (nsg_one_sub_nearProjection_psd W)
    convert this using 1; abel
  have hhi : (1 - (Uᴴ * nearProjection W * U - nearProjection W)).PosSemidef := by
    have := h1P'.add (nsg_nearProjection_psd W)
    convert this using 1; abel
  exact abs_le.2 ⟨nsf_eigenvalue_ge _ hlo i, nsf_eigenvalue_le _ hhi i⟩

/-- **`g = ½ Tr J² ≤ ½ Tr|J|`** (`U` unitary). -/
theorem nsf_conductance_le_half_nuclearNorm {U : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hU : Uᴴ * U = 1) :
    nsgConductance U ≤ nuclearNorm (Uᴴ * nearProjection W * U - nearProjection W) / 2 := by
  have hJ := nsf_current_isHermitian U
  unfold nsgConductance
  rw [ns_trace_pow_re _ hJ, nsf_nuclearNorm_eq hJ]
  gcongr with i
  have h := nsf_current_eigenvalues_abs_le_one hU i
  rw [← sq_abs]
  nlinarith [abs_nonneg (hJ.eigenvalues i)]

/-!
## On the stop
-/

/-- Before the stop, at lengths `j ≥ εW`, the trace load is at most `K`. -/
theorem nsf_traceLoad_le_of_alive {b E : ℝ} {nT nI : ℕ} {k : Fin nT → ℕ}
    {q : Fin nI → ℝ → ℝ} {K ε : ℝ} {j : ℕ} {ω : GrowthPath W} (h : ω ∈ alive b E k q K ε W j)
    (hj : ε * W ≤ j) : traceLoad b E k q W j ω ≤ K := by
  rw [tcw_mem_alive_iff] at h
  exact not_lt.1 fun hK => h j le_rfl ⟨hj, hK⟩

/-- The trace load of the one-source family: `Tr Q + Tr|J|`. -/
theorem nsf_traceLoad_eq (b E : ℝ) (κ : Fin 0 → ℕ) (q : ℝ → ℝ) (j : ℕ) (ω : GrowthPath W) :
    traceLoad b E κ (fun _ : Fin 1 => q) W j ω =
      (intervalSource b E W j q ω).trace.re + nuclearNorm (pathCurrent b E W j ω) := by
  unfold traceLoad sourceTrace
  simp [sourceLetter, letterMatrix, Fintype.sum_sum_type]

/-- **The clock and the conductance on the trace stop**: before the stop, at `j ≥ εW`, with
`q ≥ 0` and `𝕊` unitary: `Tr|J| ≤ K`, `g ≤ K/2`, `Tr Q ≤ K`, `Tr A ≤ K`. -/
theorem nsf_alive_bounds {b E : ℝ} (κ : Fin 0 → ℕ) {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x) {K ε : ℝ}
    {j : ℕ} {ω : GrowthPath W} (h : ω ∈ alive b E κ (fun _ : Fin 1 => q) K ε W j)
    (hj : ε * W ≤ j) (hS : (scatteringMatrix b E W j ω)ᴴ * scatteringMatrix b E W j ω = 1) :
    nuclearNorm (pathCurrent b E W j ω) ≤ K ∧
      nsgConductance (scatteringMatrix b E W j ω) ≤ K / 2 ∧
      (intervalSource b E W j q ω).trace.re ≤ K ∧
      (nearClock b E W j q ω).trace.re ≤ K := by
  have hL := nsf_traceLoad_le_of_alive h hj
  rw [nsf_traceLoad_eq] at hL
  have hQ := trace_intervalSource_re_nonneg b E W j q hq ω
  have hJ : 0 ≤ nuclearNorm (pathCurrent b E W j ω) := by
    unfold nuclearNorm
    exact Multiset.sum_nonneg fun x hx => by
      obtain ⟨z, -, rfl⟩ := Multiset.mem_map.1 hx
      exact norm_nonneg z
  have hA := trace_nearClock_le b E W j q hq ω
  have hg := nsf_conductance_le_half_nuclearNorm hS
  refine ⟨by linarith, ?_, by linarith, by linarith⟩
  have : nuclearNorm ((scatteringMatrix b E W j ω)ᴴ * nearProjection W *
      scatteringMatrix b E W j ω - nearProjection W) = nuclearNorm (pathCurrent b E W j ω) := rfl
  rw [this] at hg
  linarith

/-- Each eigenvalue of a PSD matrix is at most its trace. -/
theorem nsf_eigenvalue_le_trace {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.PosSemidef) (i : n) : hA.1.eigenvalues i ≤ A.trace.re := by
  have h := hA.1.trace_eq_sum_eigenvalues
  have hre : A.trace.re = ∑ k, hA.1.eigenvalues k := by
    rw [h, Complex.re_sum]; simp
  rw [hre]
  exact Finset.single_le_sum (f := fun k => hA.1.eigenvalues k)
    (fun k _ => hA.eigenvalues_nonneg k) (Finset.mem_univ i)

end BlockBand.Endpoints
