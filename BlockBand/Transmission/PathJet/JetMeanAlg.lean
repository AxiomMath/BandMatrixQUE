module

public import BlockBand.Transmission.PathJet.Statement
public import BlockBand.Transmission.PathJet.DiskMeanStrict
public import BlockBand.Transmission.PathJet.JetFlucMain
public import BlockBand.Transmission.PassiveLayer.TMMain

/-!
# The differentiated mean map: exact algebra and the contraction bound

Notation (all complex): `u, v` the mean port/physical traces at `z`, `u', v'` their
`w`-derivatives, `D = z - bv`, `φ = f'(ζ)` the old jet at `ζ`, `r₁ = uD - 1` and `r₁', r₂'`
the derivatives of the two mean-equation residuals, `k = k₋ = c + b²a²`.

* `jet_identity`: from `uD = 1 + r₁`, `r₁' = u'D + u - buv'`, `r₂' = v'(1+cφ) + bφu'` and
  the stationarity `ks² + (1+ca²)s + a² = 0`,
  `(u' - s)(1 + (c+b²u²)φ) = ε - (φ - s)(sk + a²c) - (u² - a²)(sb²φ + 1 + cφ)`,
  `ε = r₁'u(1+cφ) - u'r₁(1+cφ) + bu²r₂'`. At `r = 0` this is the first-jet map of the paper.
* `stationary_slope`: `(sk + a²c)(1 + ks) = -b²a⁴`, so `|sk + a²c| = b²/|1+ks|` when `|a| = 1`;
  this is the derivative `b²/|1+k₋s|²` of the jet map at its fixed point.
* `jet_contraction`: if `|1 + ks| ≥ b + g` and `|1 + (c+b²u²)φ| ≥ b + g/2`, then
  `|u' - s| ≤ ρ_J|φ - s| + (|ε| + |u²-a²| |sb²φ + 1 + cφ|)/(b + g/2)`,
  `ρ_J = b²/((b+g)(b+g/2)) < 1`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PathJet

/-- The jet contraction factor `ρ_J = b²/((b+g)(b+g/2))`. -/
def rhoJ (b g : ℝ) : ℝ := b ^ 2 / ((b + g) * (b + g / 2))

theorem rhoJ_nonneg {b g : ℝ} (hb : 0 < b) (hg : 0 < g) : 0 ≤ rhoJ b g := by
  unfold rhoJ; positivity

theorem rhoJ_lt_one {b g : ℝ} (hb : 0 < b) (hg : 0 < g) : rhoJ b g < 1 := by
  unfold rhoJ
  rw [div_lt_one (by positivity)]
  nlinarith

theorem jet_identity {a s k c b u u' v' D φ r₁ r₁' r₂' : ℂ}
    (hk : k = c + b ^ 2 * a ^ 2) (hs : k * s ^ 2 + (1 + c * a ^ 2) * s + a ^ 2 = 0)
    (hD : u * D = 1 + r₁) (h1 : r₁' = u' * D + u - b * u * v')
    (h2 : r₂' = v' * (1 + c * φ) + b * φ * u') :
    (u' - s) * (1 + (c + b ^ 2 * u ^ 2) * φ) =
      (r₁' * u * (1 + c * φ) - u' * r₁ * (1 + c * φ) + b * u ^ 2 * r₂') -
        (φ - s) * (s * k + a ^ 2 * c) - (u ^ 2 - a ^ 2) * (s * b ^ 2 * φ + 1 + c * φ) := by
  subst hk
  linear_combination -(u * (1 + c * φ)) * h1 - (b * u ^ 2) * h2 - (u' * (1 + c * φ)) * hD - hs

theorem stationary_slope {a s k c b : ℂ} (hk : k = c + b ^ 2 * a ^ 2)
    (hs : k * s ^ 2 + (1 + c * a ^ 2) * s + a ^ 2 = 0) :
    (s * k + a ^ 2 * c) * (1 + k * s) = -(b ^ 2 * a ^ 4) := by
  subst hk
  linear_combination (c + b ^ 2 * a ^ 2) * hs

theorem jet_contraction {a s k c b u u' φ ε : ℂ} {br g : ℝ} (hbr : 0 < br) (hg : 0 < g)
    (hbb : ‖b‖ = br) (ha : ‖a‖ = 1) (hk : k = c + b ^ 2 * a ^ 2)
    (hs : k * s ^ 2 + (1 + c * a ^ 2) * s + a ^ 2 = 0)
    (hks : br + g ≤ ‖1 + k * s‖) (hDen : br + g / 2 ≤ ‖1 + (c + b ^ 2 * u ^ 2) * φ‖)
    (hid : (u' - s) * (1 + (c + b ^ 2 * u ^ 2) * φ) =
      ε - (φ - s) * (s * k + a ^ 2 * c) - (u ^ 2 - a ^ 2) * (s * b ^ 2 * φ + 1 + c * φ)) :
    ‖u' - s‖ ≤ rhoJ br g * ‖φ - s‖ +
      (‖ε‖ + ‖u ^ 2 - a ^ 2‖ * ‖s * b ^ 2 * φ + 1 + c * φ‖) / (br + g / 2) := by
  have hL : 0 < br + g / 2 := by positivity
  have hσ : ‖s * k + a ^ 2 * c‖ * ‖1 + k * s‖ = br ^ 2 := by
    rw [← norm_mul, stationary_slope hk hs, norm_neg, norm_mul, norm_pow, norm_pow, ha, hbb]
    ring
  have hσ' : ‖s * k + a ^ 2 * c‖ ≤ br ^ 2 / (br + g) := by
    rw [le_div_iff₀ (by positivity)]
    calc ‖s * k + a ^ 2 * c‖ * (br + g) ≤ ‖s * k + a ^ 2 * c‖ * ‖1 + k * s‖ := by gcongr
      _ = br ^ 2 := hσ
  have hmain : ‖u' - s‖ * (br + g / 2) ≤
      ‖ε‖ + ‖s * k + a ^ 2 * c‖ * ‖φ - s‖ + ‖u ^ 2 - a ^ 2‖ * ‖s * b ^ 2 * φ + 1 + c * φ‖ := by
    calc ‖u' - s‖ * (br + g / 2) ≤ ‖u' - s‖ * ‖1 + (c + b ^ 2 * u ^ 2) * φ‖ := by gcongr
      _ = ‖(u' - s) * (1 + (c + b ^ 2 * u ^ 2) * φ)‖ := (norm_mul _ _).symm
      _ ≤ _ := by
        rw [hid]
        have e1 := norm_sub_le (ε - (φ - s) * (s * k + a ^ 2 * c))
          ((u ^ 2 - a ^ 2) * (s * b ^ 2 * φ + 1 + c * φ))
        have e2 := norm_sub_le ε ((φ - s) * (s * k + a ^ 2 * c))
        rw [norm_mul] at e1 e2
        linarith [mul_comm ‖φ - s‖ ‖s * k + a ^ 2 * c‖]
  have hφ0 := norm_nonneg (φ - s)
  have hρ : ‖s * k + a ^ 2 * c‖ / (br + g / 2) ≤ rhoJ br g := by
    rw [rhoJ, ← div_div]
    exact div_le_div_of_nonneg_right hσ' hL.le
  rw [← le_div_iff₀ hL] at hmain
  calc ‖u' - s‖ ≤ (‖ε‖ + ‖s * k + a ^ 2 * c‖ * ‖φ - s‖ +
        ‖u ^ 2 - a ^ 2‖ * ‖s * b ^ 2 * φ + 1 + c * φ‖) / (br + g / 2) := hmain
    _ = ‖s * k + a ^ 2 * c‖ / (br + g / 2) * ‖φ - s‖ +
        (‖ε‖ + ‖u ^ 2 - a ^ 2‖ * ‖s * b ^ 2 * φ + 1 + c * φ‖) / (br + g / 2) := by ring
    _ ≤ _ := by gcongr

end BlockBand.Transmission.PathJet
