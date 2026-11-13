module

public import BlockBand.Diffusion.Base.TransitionLawCK
public import BlockBand.Diffusion.Kernel.McKeanPDESemigroup
public import BlockBand.Diffusion.Duality.TransportProduct

/-!
# The transition law of the base diffusion, unconditionally

The two named intermediate statements `McKeanBackwardFacts D0` and `TimeMollifyDuality D0` hold for
every `D0 > 0`. Hence, for every `D0 > 0`:
* `exLbkBaseTransitionLaw_holds`: the transition law `ExLbkBaseTransitionLaw D0`;
* `exLbkCornerCKX_holds`: the corner Chapman–Kolmogorov identity `ExLbkCornerCKX D0`.
-/

set_option autoImplicit false

@[expose] public section

namespace BlockBand.Diffusion

/-- `McKeanBackwardFacts` from the McKean backward equation for the semigroup. -/
theorem mcKeanBackwardFacts_holds (D0 : ℝ) (hD0 : 0 < D0) : McKeanBackwardFacts D0 :=
  fun f hf _ hM => ⟨mkU1 D0 f, mkU2 D0 f, mkUT D0 f, fun _ _ ht hx =>
    ⟨mk_hasDerivAt_u_x hD0 hf hM ht hx, mk_hasDerivAt_u1_x hD0 hf hM ht hx,
      mk_hasDerivAt_u_t hD0 hf hM ht hx, mk_u_pde hD0 hf hM ht hx⟩,
    (mk_u_derivs_continuousOn hD0 hf hM).2⟩

/-- `TimeMollifyDuality` from the product duality `IsExBaseDiffusion.condExp_duality_product`. -/
theorem timeMollifyDuality_holds (D0 : ℝ) (hD0 : 0 < D0) : TimeMollifyDuality D0 :=
  fun _ _ _ _ _ _ h _ _ _ _ _ _ _ _ _ hX hY hXpde hYpde hXc hYc hX0 hY0
      _ _ hCX hCY _ hst =>
    h.condExp_duality_product hD0 ⟨hX.1, hX.2, hX.3, hX.4, hX.5, hX.6, hX.7⟩
      ⟨hY.1, hY.2, hY.3, hY.4, hY.5, hY.6, hY.7⟩ hXpde hYpde hXc hYc hX0 hY0 hCX hCY hst

/-- **The transition law of the base diffusion** `ExLbkBaseTransitionLaw D0`, with no conditions. -/
theorem exLbkBaseTransitionLaw_holds (D0 : ℝ) (hD0 : 0 < D0) : ExLbkBaseTransitionLaw D0 :=
  exBaseTransitionLaw_of hD0 (mcKeanBackwardFacts_holds D0 hD0) (timeMollifyDuality_holds D0 hD0)

/-- The corner Chapman–Kolmogorov identity `ExLbkCornerCKX D0`, with no conditions. -/
theorem exLbkCornerCKX_holds (D0 : ℝ) (hD0 : 0 < D0) : ExLbkCornerCKX D0 :=
  exLbkCornerCKX_of hD0 (mcKeanBackwardFacts_holds D0 hD0) (timeMollifyDuality_holds D0 hD0)

end BlockBand.Diffusion
