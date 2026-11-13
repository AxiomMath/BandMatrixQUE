module

public import BlockBand.SourceProcess.FullSourceStops.PolyEval
public import BlockBand.SourceProcess.FullSourceStops.CurrentCarrier
public import BlockBand.SourceProcess.ContractingWords.Alive

/-!
# Ordinary trace polynomials are bounded before the trace stop

The word load is at most `1 + L + L²` with `L = traceLoad`, so on the survival event before the
trace stop every ordinary trace polynomial is bounded by a constant depending on the stop level.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceGenerator

open Matrix MeasureTheory
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.SourceProcess.FullSourceStops

theorem nuclearNorm_nonneg' {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) :
    0 ≤ nuclearNorm M :=
  Multiset.sum_nonneg fun x hx => by
    obtain ⟨z, -, rfl⟩ := Multiset.mem_map.mp hx; exact norm_nonneg z

theorem trace_mul_self_re_le {n : Type*} [Fintype n] [DecidableEq n] {J : Matrix n n ℂ}
    (hJ : J.IsHermitian) : (J * J).trace.re ≤ nuclearNorm J ^ 2 := by
  rw [nuclearNorm_eq_sum_abs hJ]
  set U : Matrix n n ℂ := (hJ.eigenvectorUnitary : Matrix n n ℂ)
  set D : Matrix n n ℂ := diagonal fun i => ((hJ.eigenvalues i : ℝ) : ℂ)
  have hJ' : J = U * D * Uᴴ := conj_eigen hJ
  have hUU : Uᴴ * U = 1 := unitary_star_mul _
  have htr : (J * J).trace = (D * D).trace := by
    rw [hJ']
    calc (U * D * Uᴴ * (U * D * Uᴴ)).trace = (U * (D * D * Uᴴ)).trace := by
          rw [show U * D * Uᴴ * (U * D * Uᴴ) = U * D * (Uᴴ * U) * D * Uᴴ by
            simp only [Matrix.mul_assoc], hUU]
          simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = (D * D * Uᴴ * U).trace := by rw [Matrix.trace_mul_comm, Matrix.mul_assoc]
      _ = (D * D).trace := by rw [Matrix.mul_assoc, hUU, Matrix.mul_one]
  rw [htr, diagonal_mul_diagonal, trace_diagonal, Complex.re_sum]
  simp only [← Complex.ofReal_mul, Complex.ofReal_re]
  set S := ∑ i, |hJ.eigenvalues i|
  calc ∑ i, hJ.eigenvalues i * hJ.eigenvalues i = ∑ i, |hJ.eigenvalues i| * |hJ.eigenvalues i| :=
        Finset.sum_congr rfl fun i _ => (abs_mul_abs_self _).symm
    _ ≤ ∑ i, |hJ.eigenvalues i| * S := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (Finset.single_le_sum (f := fun i => |hJ.eigenvalues i|)
          (fun j _ => abs_nonneg _) (Finset.mem_univ i)) (abs_nonneg _)
    _ = S ^ 2 := by rw [← Finset.sum_mul, sq]

variable {W nT nI : ℕ}

/-- **The word load is at most `1 + L + L²`**, `L = traceLoad`. -/
theorem ae_wordLoad_le {b E : ℝ} (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) (hW : 1 ≤ W)
    (q : Fin nI → ℝ → ℝ) (hq : IsIntervalTests q) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ (j : ℕ) (k : Fin nT → ℕ),
      wordLoad b E k q W j ω ≤
        1 + traceLoad b E k q W j ω + traceLoad b E k q W j ω ^ 2 := by
  filter_upwards [ae_scattering_unitary hb hE1 hE2 hW] with ω hω j k
  have hg := (hω j).2
  have hJ := ContractingWords.pathCurrent_isHermitian b E j ω
  have h1 := trace_mul_self_re_le hJ
  have hS : 0 ≤ ∑ a, sourceTrace b E k q W j ω a :=
    Finset.sum_nonneg fun a _ => sourceTrace_nonneg b E k q hq j ω a
  have hN := nuclearNorm_nonneg' (pathCurrent b E W j ω)
  simp only [wordLoad, traceLoad, hg, sq] at h1 ⊢
  nlinarith

/-- **Before the stop, ordinary polynomials are bounded.** -/
theorem ae_polyValue_le_of_alive {b E : ℝ} (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (hW : 1 ≤ W) (q : Fin nI → ℝ → ℝ) (hq : IsIntervalTests q) (K ε : ℝ) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ (j : ℕ) (k : Fin nT → ℕ) (Ψ : TracePoly nT nI),
      Ψ ∈ ordPoly nT nI → ε * W ≤ j → ω ∈ alive b E k q K ε W j →
        ‖polyValue b E k q W j ω Ψ‖ ≤ polyConst Ψ * (1 + K + K ^ 2) ^ polyExp Ψ := by
  filter_upwards [ae_norm_polyValue_ord_le (nT := nT) hb hE1 hE2 hW q hq,
    ae_wordLoad_le (nT := nT) hb hE1 hE2 hW q hq, one_le_wordLoad_ae (nT := nT) hb hE1 hE2 hW q hq]
    with ω h1 h2 h3 j k Ψ hΨ hj hA
  have hL : traceLoad b E k q W j ω ≤ K := by
    rw [ContractingWords.alive_eq] at hA
    have := Set.mem_iInter₂.mp hA j (Finset.mem_range.mpr (Nat.lt_succ_self j))
    simp only [Set.mem_ofPred_eq, not_and, not_lt] at this
    exact this hj
  have hL0 : 0 ≤ traceLoad b E k q W j ω :=
    add_nonneg (Finset.sum_nonneg fun a _ => sourceTrace_nonneg b E k q hq j ω a)
      (nuclearNorm_nonneg' _)
  have hwl : wordLoad b E k q W j ω ≤ 1 + K + K ^ 2 :=
    (h2 j k).trans (by nlinarith)
  refine (h1 j k Ψ hΨ).trans (mul_le_mul_of_nonneg_left ?_ (polyConst_nonneg Ψ))
  exact pow_le_pow_left₀ (by linarith [h3 j k]) hwl _

end BlockBand.SourceProcess.FullSourceGenerator
