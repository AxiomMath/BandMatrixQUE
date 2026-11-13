module

public import BlockBand.Diffusion.Heat.Identity

/-!
# The corner heat identity

Imports the proof of the corner heat identity for the base kernel:
* kernel facts; Dynkin's formula, Fubini and the approximate identity through the base diffusion;
  `C_c^∞` truncations of `e^{-l(x+y)}`;
* `ch_chP_chExp`: the forward equation for `e^{-l(x+y)}`;
* `ch_chP_chHL`: the corner identity at finite cutoff;
* `ch_tendsto_chP_chPhi`: the approximate corner delta;
* `chLbkCornerHeatIdentity : ∀ D0 > 0, ChLbkCornerHeatIdentity D0`, `ch_excessive`,
  `ch_lintegral_harm_lt_top`, `ch_lintegral_corner_lt_top`.
-/
