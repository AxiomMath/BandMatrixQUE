module

public import BlockBand.QUE.Assembly.PairResidual
public import BlockBand.Internal.Contracts.CoareaPalm
public import BlockBand.Internal.Contracts.Layers

/-!
# The physical angular theorem and its instance at the Fourier modes

`PhysicalAngularStatement … w` is the bound for one center family `w`; the label itself is
`PhysicalAngularLabel`: for every center family that is the Dyson center
(`Layers.IsCenterSupply w`, the Dyson centre with the bounded extension of the physical centre
theorem), under the pair law on its law-preserving extension,
for every bounded phase-invariant Lipschitz `φ` on the full unit sphere of `ℂ^{sites}` (bound `M`, Lipschitz constant `L_φ`,
Euclidean norm `CoareaPalm.l2Norm`),
`|E♯[(v*Jv - j_S(λ_α)) φ(ψ_α)]| ≤ C (M + L_φ)/W`, with `C = C_{b,T,ϑ}` chosen first, for all
`4 ≤ n ≤ TW`, models, `ϑ`-bulk ranks and adjacent pairs (no width threshold: for `W` below
any fixed `W₀` the left side is at most `2M`, since the contrast and the clipped Dyson center
`Layers.centerFormula` both lie in `[-1, 1]`). For an arbitrary center family the bound is
false, which is why the label quantifies over `IsCenterSupply` families only. `ψ_α` is the explicit ordered eigenvector
selection `physicalOrderedEigenvector` (any selection gives the same value: `φ` is phase
invariant and the eigenvalue is a.s. simple).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.QUE.PhysicalAngularReduction

open MeasureTheory BlockBand.Model.Construction BlockBand.QUE.Fourier
open BlockBand.Internal.Contracts.QUE BlockBand.Internal.Contracts.CoareaPalm
open scoped ComplexConjugate

/-- `φ` is a bounded (by `M`), `L`-Lipschitz, phase-invariant function on the unit sphere of
`ℂ^ι` (Euclidean norm). Values off the sphere are irrelevant. -/
structure IsAngularTest {ι : Type} [Fintype ι] (φ : (ι → ℂ) → ℂ) (M L : ℝ) : Prop where
  bound : ∀ ψ, l2Norm ψ = 1 → ‖φ ψ‖ ≤ M
  lipschitz : ∀ ψ ψ', l2Norm ψ = 1 → l2Norm ψ' = 1 → ‖φ ψ - φ ψ'‖ ≤ L * l2Norm (ψ - ψ')
  phase : ∀ ψ (c : ℂ), ‖c‖ = 1 → φ (c • ψ) = φ ψ

/-- The bound of the physical angular theorem at one parameter set: every bulk rank, pair and
angular test. -/
def PhysicalAngularBoundAt (p : Parameters) (θ : ℝ) (w : PairCenterFamily) (C : ℝ) : Prop :=
  ∀ (model : p.GaussianRingModel) (α : Fin p.N), IsBulkRank p θ α → ∀ i : ZMod p.n,
  ∀ (φ : (p.Site → ℂ) → ℂ) (M L : ℝ), IsAngularTest φ M L →
    ‖∫ ω, ((physicalPairContrast p α i ((w p model α i).X.Hm ω) -
          (w p model α i).center ω : ℝ) : ℂ) *
        φ (physicalOrderedEigenvector p ((w p model α i).X.Hm ω) α)
      ∂extendedPairMeasure p α i (w p model α i).X.P (w p model α i).X.Hm‖ ≤
      C * (M + L) / (p.W : ℝ)

/-- **The physical angular theorem**, for a centre family `w`: `C = C_{b,T,ϑ}` first, then every
`4 ≤ n ≤ TW`. -/
def PhysicalAngularStatement (b θ T : ℝ) (hb : 0 < b) (hb' : b < 1 / 2)
    (w : PairCenterFamily) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (n W : ℕ) (hn : 4 ≤ n) (hW : 0 < W), (n : ℝ) ≤ T * (W : ℝ) →
      PhysicalAngularBoundAt ⟨n, W, b, hn, hW, hb, hb'⟩ θ w C

/-- **The physical angular theorem**: the bound holds for every centre family that is the Dyson
centre with its domain clause (`Layers.IsCenterSupply`). -/
def PhysicalAngularLabel (b θ T : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) : Prop :=
  ∀ w : PairCenterFamily, BlockBand.Internal.Contracts.Layers.IsCenterSupply w →
    PhysicalAngularStatement b θ T hb hb' w

/-- The Fourier-mode test `ψ ↦ conj A_m(ψ)`, `A_m = Σ_k z_m^{-k} Σ_a |ψ_{(k,a)}|²`. -/
def modeTest (p : Parameters) (m : ZMod p.n) (ψ : p.Site → ℂ) : ℂ :=
  conj (mode (fun k => ((∑ a : Fin p.W, ‖ψ (k, a)‖ ^ 2 : ℝ) : ℂ)) m)

theorem modeTest_eigenvector (p : Parameters) (α : Fin p.N) (m : ZMod p.n) (H : p.SiteMatrix) :
    modeTest p m (physicalOrderedEigenvector p H α) = conj (physicalMode p α m H) := rfl

theorem l2Norm_sq {ι : Type} [Fintype ι] (ψ : ι → ℂ) : l2Norm ψ ^ 2 = ∑ x, ‖ψ x‖ ^ 2 := by
  unfold l2Norm; rw [Real.sq_sqrt (Finset.sum_nonneg fun x _ => by positivity)]

theorem norm_mode_le (p : Parameters) (f : ZMod p.n → ℂ) (m : ZMod p.n) :
    ‖mode f m‖ ≤ ∑ k, ‖f k‖ := by
  unfold mode
  simp only [ZMod.dft_apply, smul_eq_mul]
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
  rw [norm_mul]
  simp [ZMod.stdAddChar_apply]

theorem sum_blocks (p : Parameters) (g : p.Site → ℝ) :
    (∑ k : ZMod p.n, ∑ a : Fin p.W, g (k, a)) = ∑ x, g x := by
  rw [← Finset.sum_product']; rfl

/-- `conj A_m` is an angular test with bound one and Lipschitz constant two. -/
theorem modeTest_isAngularTest (p : Parameters) (m : ZMod p.n) :
    IsAngularTest (modeTest p m) 1 2 := by
  refine ⟨fun ψ hψ => ?_, fun ψ ψ' hψ hψ' => ?_, fun ψ c hc => ?_⟩
  · unfold modeTest
    rw [Complex.norm_conj]
    refine (norm_mode_le p _ m).trans (le_of_eq ?_)
    simp only [Complex.norm_real, Real.norm_eq_abs]
    rw [Finset.sum_congr rfl fun k _ => abs_of_nonneg
      (Finset.sum_nonneg fun a _ => by positivity : (0 : ℝ) ≤ ∑ a : Fin p.W, ‖ψ (k, a)‖ ^ 2)]
    rw [sum_blocks p (fun x => ‖ψ x‖ ^ 2), ← l2Norm_sq, hψ, one_pow]
  · unfold modeTest
    rw [← map_sub, Complex.norm_conj]
    have hlin : mode (fun k => ((∑ a : Fin p.W, ‖ψ (k, a)‖ ^ 2 : ℝ) : ℂ)) m -
        mode (fun k => ((∑ a : Fin p.W, ‖ψ' (k, a)‖ ^ 2 : ℝ) : ℂ)) m =
        mode (fun k => ((∑ a : Fin p.W, (‖ψ (k, a)‖ ^ 2 - ‖ψ' (k, a)‖ ^ 2) : ℝ) : ℂ)) m := by
      unfold mode
      rw [← Pi.sub_apply (ZMod.dft _) (ZMod.dft _) m, ← map_sub]
      have hfun : ((fun k => ((∑ a : Fin p.W, ‖ψ (k, a)‖ ^ 2 : ℝ) : ℂ)) -
          fun k => ((∑ a : Fin p.W, ‖ψ' (k, a)‖ ^ 2 : ℝ) : ℂ)) =
          fun k => ((∑ a : Fin p.W, (‖ψ (k, a)‖ ^ 2 - ‖ψ' (k, a)‖ ^ 2) : ℝ) : ℂ) := by
        funext k; rw [Pi.sub_apply, Finset.sum_sub_distrib]; push_cast; rfl
      rw [hfun]
    rw [hlin]
    refine (norm_mode_le p _ m).trans ?_
    simp only [Complex.norm_real, Real.norm_eq_abs]
    calc (∑ k : ZMod p.n, |∑ a : Fin p.W, (‖ψ (k, a)‖ ^ 2 - ‖ψ' (k, a)‖ ^ 2)|)
        ≤ ∑ k : ZMod p.n, ∑ a : Fin p.W, |‖ψ (k, a)‖ ^ 2 - ‖ψ' (k, a)‖ ^ 2| :=
          Finset.sum_le_sum fun k _ => Finset.abs_sum_le_sum_abs _ _
      _ = ∑ x, |‖ψ x‖ ^ 2 - ‖ψ' x‖ ^ 2| := sum_blocks p (fun x => |‖ψ x‖ ^ 2 - ‖ψ' x‖ ^ 2|)
      _ ≤ ∑ x, (‖ψ x‖ + ‖ψ' x‖) * ‖(ψ - ψ') x‖ := by
          refine Finset.sum_le_sum fun x _ => ?_
          have h1 : |‖ψ x‖ ^ 2 - ‖ψ' x‖ ^ 2| = (‖ψ x‖ + ‖ψ' x‖) * |‖ψ x‖ - ‖ψ' x‖| := by
            rw [show ‖ψ x‖ ^ 2 - ‖ψ' x‖ ^ 2 = (‖ψ x‖ + ‖ψ' x‖) * (‖ψ x‖ - ‖ψ' x‖) by ring,
              abs_mul, abs_of_nonneg (by positivity)]
          rw [h1, Pi.sub_apply]
          exact mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le _ _) (by positivity)
      _ = (∑ x, ‖ψ x‖ * ‖(ψ - ψ') x‖) + ∑ x, ‖ψ' x‖ * ‖(ψ - ψ') x‖ := by
          rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun x _ => by ring
      _ ≤ l2Norm ψ * l2Norm (ψ - ψ') + l2Norm ψ' * l2Norm (ψ - ψ') := by
          have cs := fun (u v : p.Site → ℂ) =>
            Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun x => ‖u x‖) (fun x => ‖v x‖)
          unfold l2Norm
          exact add_le_add (cs ψ (ψ - ψ')) (cs ψ' (ψ - ψ'))
      _ = 2 * l2Norm (ψ - ψ') := by rw [hψ, hψ']; ring
  · unfold modeTest
    congr 3
    funext k
    congr 2
    funext a
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, hc, one_mul]

/-- **The physical angular theorem implies `QUE.PhysicalAngularModeContract`** (as in the proof
of the QUE theorem): the instance `φ = conj A_m`, `M = 1`, `L_φ = 2`, gives
`QUE.PhysicalAngularModeContract` with `A = 3C` and no width threshold. -/
theorem physicalAngularModeContract_of_statement (b θ T : ℝ) (hb : 0 < b) (hb' : b < 1 / 2)
    (w : PairCenterFamily) (h : PhysicalAngularStatement b θ T hb hb' w) :
    PhysicalAngularModeContract b θ T hb hb' w := by
  obtain ⟨C, hC, hbound⟩ := h
  refine ⟨3 * C, 0, by positivity, ?_⟩
  intro n W hn hW hnW _ p model α hα i m hm
  have key := hbound n W hn hW hnW model α hα i (modeTest p m) 1 2
    (modeTest_isAngularTest p m)
  calc _ ≤ C * (1 + 2) / (p.W : ℝ) := key
    _ = 3 * C / (p.W : ℝ) := by ring

/-- The physical angular theorem gives `QUE.PhysicalAngularModeContract` for every Dyson centre
family. -/
theorem physicalAngularModeContract_of_label (b θ T : ℝ) (hb : 0 < b) (hb' : b < 1 / 2)
    (h : PhysicalAngularLabel b θ T hb hb') (w : PairCenterFamily)
    (hw : BlockBand.Internal.Contracts.Layers.IsCenterSupply w) :
    PhysicalAngularModeContract b θ T hb hb' w :=
  physicalAngularModeContract_of_statement b θ T hb hb' w (h w hw)

end BlockBand.QUE.PhysicalAngularReduction
