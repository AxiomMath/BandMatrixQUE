module

public import BlockBand.Diffusion.Base.Existence
public import BlockBand.Diffusion.Duality.All
public import BlockBand.Diffusion.Kernel.McKeanContinuity
public import BlockBand.Diffusion.Kernel.McKeanMass
public import BlockBand.Diffusion.Kernel.SpherePDE
public import BlockBand.Diffusion.Kernel.SphereApprox
public import BlockBand.Diffusion.Kernel.SphereMorePos

/-!
# The transition law of the base diffusion: statements

The product kernel `exKernel D0 t z z' = pX_t(x, x') pY_t(y, y')` (McKean kernel in `x`, spherical
kernel in `y`), the transition-law statement `ExLbkBaseTransitionLaw` and the corner
Chapman–Kolmogorov statement `ExLbkCornerCKX` (local copies of `LbkBaseTransitionLaw` and
`LbkCornerCKX`), and two named intermediate statements used as hypotheses by the intermediate
theorems:
* `McKeanBackwardFacts D0`: the backward equation and `C^{1,2}` regularity of the McKean
  semigroup `mkUX D0 f` (`= mkSemigroupX D0 f` for `t > 0`) on `(0,∞) × (0,∞)`, proved by
  `mcKeanBackwardFacts_holds`;
* `TimeMollifyDuality D0`: conditional space-time duality for the base diffusion and products
  `uX(τ, x) uY(τ, y)` of one-dimensional `C^{0,2}` solutions (`ExIsC02On1`, a copy of
  `IsC02On1`), the statement of `IsExBaseDiffusion.condExp_duality_product`, proved by
  `timeMollifyDuality_holds`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

/-!
### The product kernel and the target statements
-/

/-- **The explicit base kernel** `p_t(z, z') = pX_t(x, x') · pY_t(y, y')`: a copy of `lbkKernel`
with the kernels `mkKernelX`, `skKernelY`. -/
def exKernel (D0 : ℝ) (t : ℝ) (z z' : ℝ × ℝ) : ℝ :=
  mkKernelX D0 t z.1 z'.1 * skKernelY D0 t z.2 z'.2

/-- The product identity (definitional). -/
theorem exKernel_eq (D0 t : ℝ) (z z' : ℝ × ℝ) :
    exKernel D0 t z z' = mkKernelX D0 t z.1 z'.1 * skKernelY D0 t z.2 z'.2 := rfl

/-- **The one-time transition law of the base diffusion**: a copy of `LbkBaseTransitionLaw` with
`exBaseStrip`, `IsExBaseDiffusion` and `exKernel`. -/
def ExLbkBaseTransitionLaw (D0 : ℝ) : Prop :=
  ∀ t : ℝ≥0, 0 < t → ∀ z ∈ exBaseStrip,
    ∀ (Ω : Type) (m : MeasurableSpace Ω) (𝓖 : Filtration ℝ≥0 m) (P : Measure Ω)
      (Z : ℝ≥0 → Ω → ℝ × ℝ), IsExBaseDiffusion P 𝓖 D0 z Z →
      ∀ B : Set (ℝ × ℝ), MeasurableSet B →
        P (Z t ⁻¹' B) = ∫⁻ z' in B, ENNReal.ofReal (exKernel D0 t z z')

/-- The hyperbolic radial bridge mass `∫ pX_s(x,x') pX_{T-s}(x',0) dx'` (a copy of `bopXMass` with
the kernel `mkKernelX`). -/
def exBopXMass (D0 x T s : ℝ) : ℝ≥0∞ :=
  ∫⁻ x', ENNReal.ofReal (mkKernelX D0 s x x') * ENNReal.ofReal (mkKernelX D0 (T - s) x' 0)

/-- **Corner Chapman–Kolmogorov for the hyperbolic radial factor**: a copy of `LbkCornerCKX` with
`exBopXMass` and `mkKernelX`. -/
def ExLbkCornerCKX (D0 : ℝ) : Prop :=
  ∀ T s : ℝ, 0 < s → s < T → ∀ x : ℝ, 0 ≤ x →
    exBopXMass D0 x T s = ENNReal.ofReal (mkKernelX D0 T x 0)

/-!
### The McKean backward equation
-/

/-- `u(t, x) = ∫_{[0,∞)} pX_t(x, x') f(x') dx'` (equal to `mkSemigroupX D0 f (t, x)` for `t > 0`).
Its body is that of `mkU`, so `mkUX D0 f t x` and `mkU D0 f t x` are definitionally equal. -/
def mkUX (D0 : ℝ) (f : ℝ → ℝ) (t x : ℝ) : ℝ := ∫ x' in Ici (0 : ℝ), mkKernelX D0 t x x' * f x'

/-- **The McKean backward equation.** For every
measurable `f` with `|f| ≤ M`, the McKean semigroup `u = mkUX D0 f` has, at every `t > 0`,
`x > 0`, partial derivatives `∂ₓu = u1`, `∂ₓu1 = u2`, `∂ₜu = ut` (`HasDerivAt` along coordinate
lines), solves the backward equation
`∂ₜu = (D₀/2)[x(1+x)∂ₓ²u + (1+2x)∂ₓu]` (in `deriv` form, as in `mk_u_pde`), and
`u1, u2, ut` are jointly continuous on `(0,∞) × (0,∞)`. (Joint continuity of `u` itself up to
`t = 0` and `x = 0` is `mk_semigroupX_continuousOn`.)

For `0 < D0` it follows from the McKean semigroup lemmas:
```
fun f hf M hM => ⟨mkU1 D0 f, mkU2 D0 f, mkUT D0 f, fun t x ht hx =>
  ⟨mk_hasDerivAt_u_x hD0 hf hM ht hx, mk_hasDerivAt_u1_x hD0 hf hM ht hx,
    mk_hasDerivAt_u_t hD0 hf hM ht hx, mk_u_pde hD0 hf hM ht hx⟩,
  (mk_u_derivs_continuousOn hD0 hf hM).2⟩
```
(`mkU D0 f` and `mkUX D0 f` unfold to the same term). -/
def McKeanBackwardFacts (D0 : ℝ) : Prop :=
  ∀ f : ℝ → ℝ, Measurable f → ∀ M : ℝ, (∀ y, |f y| ≤ M) →
    ∃ u1 u2 ut : ℝ → ℝ → ℝ,
      (∀ t x : ℝ, 0 < t → 0 < x →
        HasDerivAt (fun z => mkUX D0 f t z) (u1 t x) x ∧
        HasDerivAt (fun z => u1 t z) (u2 t x) x ∧
        HasDerivAt (fun s => mkUX D0 f s x) (ut t x) t ∧
        deriv (fun s => mkUX D0 f s x) t =
          D0 / 2 * (x * (1 + x) * deriv (deriv fun z => mkUX D0 f t z) x +
            (1 + 2 * x) * deriv (fun z => mkUX D0 f t z) x)) ∧
      ContinuousOn (fun p : ℝ × ℝ => u1 p.1 p.2) (Ioi 0 ×ˢ Ioi 0) ∧
      ContinuousOn (fun p : ℝ × ℝ => u2 p.1 p.2) (Ioi 0 ×ˢ Ioi 0) ∧
      ContinuousOn (fun p : ℝ × ℝ => ut p.1 p.2) (Ioi 0 ×ˢ Ioi 0)

/-!
### Duality under `C^{0,2}` regularity
-/

/-- One-dimensional `C^{0,2}` data on `I × J` (curried `w τ x`): `wt`, `w1`, `w2` are `∂_τ w`,
`∂ₓ w`, `∂ₓ² w` (`HasDerivAt`), and `w, wt, w1, w2` are jointly continuous on `I × J`. Body and
field names are those of `IsC02On1`, so the two structures convert by
`⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7⟩`.
-/
structure ExIsC02On1 (w wt w1 w2 : ℝ → ℝ → ℝ) (I J : Set ℝ) : Prop where
  hasDerivAt_time : ∀ τ ∈ I, ∀ x ∈ J, HasDerivAt (fun τ => w τ x) (wt τ x) τ
  hasDerivAt_space : ∀ τ ∈ I, ∀ x ∈ J, HasDerivAt (w τ) (w1 τ x) x
  hasDerivAt_space2 : ∀ τ ∈ I, ∀ x ∈ J, HasDerivAt (w1 τ) (w2 τ x) x
  continuousOn : ContinuousOn (fun q : ℝ × ℝ => w q.1 q.2) (I ×ˢ J)
  continuousOn_time : ContinuousOn (fun q : ℝ × ℝ => wt q.1 q.2) (I ×ˢ J)
  continuousOn_space : ContinuousOn (fun q : ℝ × ℝ => w1 q.1 q.2) (I ×ˢ J)
  continuousOn_space2 : ContinuousOn (fun q : ℝ × ℝ => w2 q.1 q.2) (I ×ˢ J)

/-- **Conditional space-time duality for products of one-dimensional `C^{0,2}` solutions**, the
statement of `IsExBaseDiffusion.condExp_duality_product` (with `IsC02On1 ↦ ExIsC02On1`):
for every base diffusion `Z = (X, Y)` from `z`, every `t` and every `uX`, `uY` that are `C^{0,2}`
on `(0, t) × (0, ∞)`, resp. `(0, t) × (0, 1)`, solve the forward equations
`∂_τ uX = (D₀/2)[x(1+x)∂ₓ²uX + (1+2x)∂ₓuX]`, `∂_τ uY = (D₀/2)[y(1-y)∂ᵧ²uY + (1-2y)∂ᵧuY]` there,
are continuous on `[0, t) × (0, ∞)`, resp. `[0, t) × (0, 1)`, continuous there within at
`(t, z₁)`, resp. `(t, z₂)`, and bounded there: for `s < t`,
`E[uX(0, X_t) uY(0, Y_t) | 𝓖_s] = uX(t - s, X_s) uY(t - s, Y_s)` a.s.

For `0 < D0` it follows from the product duality:
```
fun Ω m 𝓖 P z Z h t uX uXt uX1 uX2 uY uYt uY1 uY2 hX hY hXpde hYpde hXc hYc hX0 hY0
    CX CY hCX hCY s hst =>
  h.condExp_duality_product hD0 ⟨hX.1, hX.2, hX.3, hX.4, hX.5, hX.6, hX.7⟩
    ⟨hY.1, hY.2, hY.3, hY.4, hY.5, hY.6, hY.7⟩ hXpde hYpde hXc hYc hX0 hY0 hCX hCY hst
```
(The product duality uses the product rule `isC02On_prodU`, `spGen_prodU` in `Fin 2` coordinates,
and the base duality under `C^{0,2}` regularity `condExp_duality_C02`, obtained by time
mollification from `IsTestMPSolution.condExp_duality`.) -/
def TimeMollifyDuality (D0 : ℝ) : Prop :=
  ∀ (Ω : Type) (m : MeasurableSpace Ω) (𝓖 : Filtration ℝ≥0 m) (P : Measure Ω) (z : ℝ × ℝ)
    (Z : ℝ≥0 → Ω → ℝ × ℝ), IsExBaseDiffusion P 𝓖 D0 z Z →
    ∀ (t : ℝ≥0) (uX uXt uX1 uX2 uY uYt uY1 uY2 : ℝ → ℝ → ℝ),
      ExIsC02On1 uX uXt uX1 uX2 (Ioo 0 (t : ℝ)) (Ioi 0) →
      ExIsC02On1 uY uYt uY1 uY2 (Ioo 0 (t : ℝ)) (Ioo 0 1) →
      (∀ τ ∈ Ioo 0 (t : ℝ), ∀ x ∈ Ioi (0 : ℝ),
        uXt τ x = D0 / 2 * (x * (1 + x) * uX2 τ x + (1 + 2 * x) * uX1 τ x)) →
      (∀ τ ∈ Ioo 0 (t : ℝ), ∀ y ∈ Ioo (0 : ℝ) 1,
        uYt τ y = D0 / 2 * (y * (1 - y) * uY2 τ y + (1 - 2 * y) * uY1 τ y)) →
      ContinuousOn (fun q : ℝ × ℝ => uX q.1 q.2) (Ico 0 (t : ℝ) ×ˢ Ioi 0) →
      ContinuousOn (fun q : ℝ × ℝ => uY q.1 q.2) (Ico 0 (t : ℝ) ×ˢ Ioo 0 1) →
      ContinuousWithinAt (fun q : ℝ × ℝ => uX q.1 q.2) (Ico 0 (t : ℝ) ×ˢ Ioi 0) (t, z.1) →
      ContinuousWithinAt (fun q : ℝ × ℝ => uY q.1 q.2) (Ico 0 (t : ℝ) ×ˢ Ioo 0 1) (t, z.2) →
      ∀ CX CY : ℝ, (∀ q ∈ Ico 0 (t : ℝ) ×ˢ Ioi 0, |uX q.1 q.2| ≤ CX) →
      (∀ q ∈ Ico 0 (t : ℝ) ×ˢ Ioo 0 1, |uY q.1 q.2| ≤ CY) →
      ∀ s : ℝ≥0, s < t →
        P[fun ω => uX 0 (Z t ω).1 * uY 0 (Z t ω).2 | 𝓖 s] =ᵐ[P]
          fun ω => uX (t - s) (Z s ω).1 * uY (t - s) (Z s ω).2

end BlockBand.Diffusion
