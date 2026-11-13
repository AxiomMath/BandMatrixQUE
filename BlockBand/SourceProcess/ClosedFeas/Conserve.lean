module

public import BlockBand.SourceProcess.ClosedFeas.Algebra
public import BlockBand.SourceProcess.ClosedSum.ClosedGram
public import BlockBand.SourceProcess.ClosedPath.FarStep
public import BlockBand.Transmission.Bridge.TransportFull

/-!
# The retained current is conserved by the unclosed transport

With the time-`s` data `A`, `Π` (`B = ΠᴴΠ`), the retained current at length `j` is
`physSplit j = 𝕊_jᴴ(P + B)𝕊_j - (P + A) = J_j + 𝕊_jᴴB𝕊_j - A`.
Since the far amplitudes are fixed, `J_A(t) = N*J_A(s)N`: from `J_{j+1} = NᴴJ_jN`,
`(1-P)N = 1-P` and `(1-P)𝕊_jN = (1-P)𝕊_{j+1}`,
* **`splitCurrent_transport`** (algebra): `Nᴴ splitCurrent(𝕊₀) N = splitCurrent(𝕊₁)`;
* **`ae_openCur_split`**: almost surely, if the time-`s` frame has `Vs𝖣Vsᴴ = physSplit n_s`, then
  the transported current columns `(N_{n_s}⋯N_{j-1})ᴴVs` have `X𝖣Xᴴ = physSplit j` for all
  `j ≥ n_s` (`n_s ≥ 1`);
* `frame_sig`: the probe columns of the frame have signature zero.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedFeas

open MeasureTheory Matrix BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedSum
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Transmission.Bridge BlockBand.SourceProcess.SourceProcessLaw

section Algebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {P A Pi N S₀ S₁ : Matrix ι ι ℂ}

/-- **The retained current is transported by congruence.** -/
theorem splitCurrent_transport (hAH : Aᴴ = A) (hAA : A * A = A) (hAQ : A * (1 - P) = A)
    (hPiQ : Pi * (1 - P) = Pi) (hQN : (1 - P) * N = 1 - P) (hS : (1 - P) * S₀ * N = (1 - P) * S₁)
    (hJ : S₁ᴴ * P * S₁ - P = Nᴴ * (S₀ᴴ * P * S₀ - P) * N) :
    Nᴴ * splitCurrent S₀ P A Pi * N = splitCurrent S₁ P A Pi := by
  have hAN : A * N = A := by rw [← hAQ, Matrix.mul_assoc, hQN]
  have hNAN : Nᴴ * A * N = A := by
    calc Nᴴ * A * N = (A * N)ᴴ * (A * N) := by
          rw [conjTranspose_mul, hAH, ← Matrix.mul_assoc, Matrix.mul_assoc Nᴴ A A, hAA]
      _ = A := by rw [hAN, hAH, hAA]
  have hPiS : Pi * S₀ * N = Pi * S₁ := by
    calc Pi * S₀ * N = Pi * ((1 - P) * S₀ * N) := by
          conv_lhs => rw [← hPiQ]
          simp only [Matrix.mul_assoc]
      _ = Pi * S₁ := by rw [hS, ← Matrix.mul_assoc, hPiQ]
  have hB : Nᴴ * (S₀ᴴ * (Piᴴ * Pi) * S₀) * N = S₁ᴴ * (Piᴴ * Pi) * S₁ := by
    calc Nᴴ * (S₀ᴴ * (Piᴴ * Pi) * S₀) * N = (Pi * S₀ * N)ᴴ * (Pi * S₀ * N) := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hPiS]; simp only [conjTranspose_mul, Matrix.mul_assoc]
  have e : ∀ S : Matrix ι ι ℂ, splitCurrent S P A Pi =
      (Sᴴ * P * S - P) + Sᴴ * (Piᴴ * Pi) * S - A := by
    intro S
    simp only [splitCurrent, Matrix.mul_add, Matrix.add_mul]
    abel
  have hsplit : Nᴴ * ((S₀ᴴ * P * S₀ - P) + S₀ᴴ * (Piᴴ * Pi) * S₀ - A) * N =
      Nᴴ * (S₀ᴴ * P * S₀ - P) * N + Nᴴ * (S₀ᴴ * (Piᴴ * Pi) * S₀) * N - Nᴴ * A * N := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul]
  rw [e, e, hsplit, hB, hNAN, hJ]

end Algebra

variable {W : ℕ}

/-- The current signature `diag(±1)` on `Fin K × Fin 2`. -/
def curSig (K : ℕ) : Matrix (Fin K × Fin 2) (Fin K × Fin 2) ℂ :=
  diagonal fun c => if c.2 = 0 then 1 else -1

/-- The time-`s` omitted far inputs `A` (embedded). -/
abbrev omA (b E s h : ℝ) (W : ℕ) (ω : GrowthPath W) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  farEmbed (omittedProj b E h W (closeLen s W) ω)

/-- The time-`s` pairing `Π` (embedded). -/
abbrev omPi (b E s h : ℝ) (W : ℕ) (ω : GrowthPath W) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  farEmbed (closingPairing b E h W (closeLen s W) ω)

/-- **The retained current at length `j`** with the time-`s` closing data. -/
def physSplit (b E s h : ℝ) (W j : ℕ) (ω : GrowthPath W) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  splitCurrent (scatteringMatrix b E W j ω) (nearPortProj W) (omA b E s h W ω) (omPi b E s h W ω)

theorem farEmbed_mul_one_sub (X : Matrix (Fin W) (Fin W) ℂ) :
    farEmbed X * (1 - nearPortProj W) = farEmbed X := by
  rw [Matrix.mul_sub, Matrix.mul_one, farEmbed_mul_nearPortProj, sub_zero]

/-- **The transported current columns carry the retained current**, almost surely. -/
theorem ae_openCur_split {b E s h : ℝ} {K : ℕ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E)
    (hE2 : E < 2) (hW : 1 ≤ W) (hs : 1 ≤ closeLen s W) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ Vs : Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ,
      Vs * curSig K * Vsᴴ = physSplit b E s h W (closeLen s W) ω → ∀ m : ℕ,
      (stepProd (fun i => transportN b E W i ω) (closeLen s W) m)ᴴ * Vs * curSig K *
          ((stepProd (fun i => transportN b E W i ω) (closeLen s W) m)ᴴ * Vs)ᴴ =
        physSplit b E s h W (closeLen s W + m) ω := by
  filter_upwards [ae_pathCurrent_succ_full hb0 hb hE1 hE2 hW, ae_farOut_succ hb0 hb hE1 hE2 hW]
    with ω hJ hF Vs h0 m
  induction m with
  | zero => simpa [stepProd] using h0
  | succ m ih =>
    have hj : 1 ≤ closeLen s W + m := le_trans hs (Nat.le_add_right _ _)
    have step := splitCurrent_transport (P := nearPortProj W) (A := omA b E s h W ω)
      (Pi := omPi b E s h W ω)
      (by rw [farEmbed_conjTranspose, omittedProj_conjTranspose])
      (by rw [farEmbed_mul, omittedProj_mul_self]) (farEmbed_mul_one_sub _)
      (farEmbed_mul_one_sub _) (one_sub_nearPortProj_mul_transportN _ ω) (hF _ hj) (hJ _ hj)
    rw [show closeLen s W + (m + 1) = closeLen s W + m + 1 by omega, physSplit, ← step]
    change _ = _ * physSplit b E s h W (closeLen s W + m) ω * _
    rw [← ih]
    simp only [stepProd, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]

/-- The current block of `openFrameAt` is the transported time-`s` frame. -/
theorem curBlock_openFrameAt {p M K : ℕ} (b E s T : ℝ) (q : Fin p → ℝ → ℝ) (j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (x : SampledPath W p M) :
    curBlock (openFrameAt b E s T q W j Vs x) =
      (stepProd (fun i => transportN b E W i x.1) (closeLen s W) (j - closeLen s W))ᴴ * Vs x.1 := by
  ext z k; simp [curBlock, openFrameAt]

/-- **Probe columns have signature zero**: `V𝖣Vᴴ` only sees the current block. -/
theorem frame_sig {ι π : Type*} [Fintype ι] [Fintype π] [DecidableEq π] {K : ℕ}
    (V : Matrix ι (SrcCol K π) ℂ) :
    V * srcSignature K π * Vᴴ = curBlock V * curSig K * (curBlock V)ᴴ := by
  ext x y
  simp only [mul_apply, srcSignature, curSig, diagonal_apply, curBlock, of_apply,
    conjTranspose_apply, Fintype.sum_sum_type, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_mul, zero_mul]
  simp

end BlockBand.SourceProcess.ClosedFeas
