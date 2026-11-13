module

public import BlockBand.SourceProcess.FullSource.Estimates
public import BlockBand.Transmission.PathScalar.All

/-!
# Joint measurability of the one-layer transport objects

The one-layer objects (Schur complements, resolvents, `Δ`, the transport `N`, the Ward noise and
`D₊`) are jointly measurable in the old two-port matrix and the fresh layer.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSource

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.Transmission.PathScalar

variable {W : ℕ} {α : Type*} [MeasurableSpace α]

theorem measurable_portBlock_comp {XX : α → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hXX : Measurable XX) (i j : Fin 2) : Measurable fun a => portBlock (XX a) i j :=
  Measurable.of_eval_matrix _ fun _ _ => hXX.eval_matrix

theorem measurable_nearSchur_comp (z : ℂ) {XX : α → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hXX : Measurable XX) : Measurable fun a => nearSchur z (XX a) := by
  have hY := measurable_portBlock_comp hXX
  have hinv : Measurable fun a =>
      (z • (1 : Matrix (Fin W) (Fin W) ℂ) - portBlock (XX a) 1 1)⁻¹ := by
    refine measurable_matrix_inv.comp (Measurable.of_eval_matrix _ fun x y => ?_)
    simp only [Matrix.sub_apply]
    exact measurable_const.sub (hY 1 1).eval_matrix
  refine Measurable.of_eval_matrix _ fun x y => ?_
  simp only [nearSchur, Matrix.add_apply]
  exact (hY 0 0).eval_matrix.add
    (measurable_matrix_mul' (measurable_matrix_mul' (hY 0 1) hinv) (hY 1 0)).eval_matrix

theorem measurable_twoPortResolvent_comp (b E : ℝ)
    {XX : α → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hXX : Measurable XX) :
    Measurable fun a => twoPortResolvent b E (XX a) := by
  refine measurable_matrix_inv.comp (Measurable.of_eval_matrix _ fun x y => ?_)
  simp only [Matrix.sub_apply]
  exact measurable_const.sub hXX.eval_matrix

theorem measurable_freshLayer_comp (b E : ℝ) {X : α → Matrix (Fin W) (Fin W) ℂ}
    {ω : α → LayerSample W .oneBlockOnePort} (hX : Measurable X) (hω : Measurable ω) :
    Measurable fun a => freshLayer b E (X a) (ω a) := by
  have hB := measurable_bondMatrix .oneBlockOnePort (measurable_snd.comp hω)
  have hD := measurable_blockDiag (W := W) (measurable_fst.comp hω)
  have hM : Measurable fun a => layerMatrix .oneBlockOnePort E (boundaryZ b E)
      (Matrix.of fun (u v : Fin 1 × Fin W) => X a u.2 v.2) (ω a) := by
    refine Measurable.of_eval_matrix _ fun x y => ?_
    rcases x with x | x <;> rcases y with y | y <;>
      simp only [layerMatrix, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.sub_apply, Matrix.of_apply]
    · exact (hD.eval_matrix.sub measurable_const).sub hX.eval_matrix
    · exact hB.eval_matrix
    · exact (measurable_matrix_conjTranspose' hB).eval_matrix
    · exact measurable_const
  exact measurable_matrix_inv.comp hM

theorem measurable_freshBlock_comp (b E : ℝ) {X : α → Matrix (Fin W) (Fin W) ℂ}
    {ω : α → LayerSample W .oneBlockOnePort} (hX : Measurable X) (hω : Measurable ω)
    (i j : Bool) : Measurable fun a => freshBlock b E (X a) (ω a) i j :=
  Measurable.of_eval_matrix _ fun _ _ => (measurable_freshLayer_comp b E hX hω).eval_matrix

theorem measurable_freshL_comp (b E : ℝ) {X : α → Matrix (Fin W) (Fin W) ℂ}
    {ω : α → LayerSample W .oneBlockOnePort} (hX : Measurable X) (hω : Measurable ω) :
    Measurable fun a => freshL b E (X a) (ω a) := by
  have hK : Measurable fun a => boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X a :=
    Measurable.of_eval_matrix _ fun x y => by
      simp only [Matrix.sub_apply]; exact measurable_const.sub hX.eval_matrix
  exact measurable_matrix_mul' hK (Measurable.of_eval_matrix _ fun _ _ =>
    (measurable_freshLayer_comp b E hX hω).eval_matrix)

theorem measurable_freshDelta_comp (b E : ℝ) {X : α → Matrix (Fin W) (Fin W) ℂ}
    {ω : α → LayerSample W .oneBlockOnePort} (hX : Measurable X) (hω : Measurable ω) :
    Measurable fun a => freshDelta b E (X a) (ω a) := by
  have hK : Measurable fun a => boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X a :=
    Measurable.of_eval_matrix _ fun x y => by
      simp only [Matrix.sub_apply]; exact measurable_const.sub hX.eval_matrix
  have hG : Measurable fun a => (Matrix.of fun x y => freshLayer b E (X a) (ω a)
      (Sum.inl ((0 : Fin 1), x)) (Sum.inl ((0 : Fin 1), y)) : Matrix (Fin W) (Fin W) ℂ) :=
    Measurable.of_eval_matrix _ fun _ _ => (measurable_freshLayer_comp b E hX hω).eval_matrix
  refine Measurable.of_eval_matrix _ fun x y => ?_
  simp only [freshDelta, Matrix.sub_apply]
  exact (measurable_matrix_mul' (measurable_matrix_mul' hK hG) hK).eval_matrix.sub
    hK.eval_matrix

theorem measurable_freshTransport_comp (b E : ℝ)
    {XX : α → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} {ω : α → LayerSample W .oneBlockOnePort}
    (hXX : Measurable XX) (hω : Measurable ω) :
    Measurable fun a => freshTransport b E (XX a) (ω a) := by
  have hX := measurable_nearSchur_comp (boundaryZ b E) hXX
  have hL := measurable_freshL_comp b E hX hω
  have hDR := measurable_matrix_mul' (measurable_freshDelta_comp b E hX hω)
    (measurable_portBlock_comp (measurable_twoPortResolvent_comp b E hXX) 0 1)
  refine Measurable.of_eval_matrix _ fun x y => ?_
  simp only [freshTransport, Matrix.of_apply]
  split_ifs
  · exact hL.eval_matrix
  · exact hDR.eval_matrix
  · exact measurable_const
  · exact measurable_const

theorem measurable_wardNoise_comp (b E : ℝ)
    {XX : α → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} {ω : α → LayerSample W .oneBlockOnePort}
    (hXX : Measurable XX) (hω : Measurable ω) :
    Measurable fun a => wardNoise b E (XX a) (ω a) := by
  have hN := measurable_freshTransport_comp b E hXX hω
  refine Measurable.of_eval_matrix _ fun x y => ?_
  simp only [wardNoise, Matrix.sub_apply]
  exact (measurable_matrix_mul' hN (measurable_matrix_conjTranspose' hN)).eval_matrix.sub
    measurable_const

theorem measurable_freshD_comp (b E : ℝ)
    {XX : α → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} {ω : α → LayerSample W .oneBlockOnePort}
    (hXX : Measurable XX) (hω : Measurable ω) :
    Measurable fun a => freshD b E (XX a) (ω a) := by
  have hX := measurable_nearSchur_comp (boundaryZ b E) hXX
  have hK : Measurable fun a => boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) -
      nearSchur (boundaryZ b E) (XX a) :=
    Measurable.of_eval_matrix _ fun x y => by
      simp only [Matrix.sub_apply]; exact measurable_const.sub hX.eval_matrix
  have h2 := measurable_matrix_mul' (measurable_matrix_mul'
    (measurable_freshBlock_comp b E hX hω true true) hK)
    (measurable_portBlock_comp (measurable_twoPortResolvent_comp b E hXX) 0 1)
  refine Measurable.of_eval_matrix _ fun x c => ?_
  simp only [freshD]
  split_ifs
  · exact (measurable_freshBlock_comp b E hX hω true false).eval_matrix
  · exact h2.eval_matrix

end BlockBand.SourceProcess.FullSource
