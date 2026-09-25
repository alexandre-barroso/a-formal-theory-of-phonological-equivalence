import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
namespace AccentRegion
structure Weights where
  clash : ℝ
  dep : ℝ
  deplink : ℝ
  dep_acc : ℝ
  dock_prev : ℝ
  float : ℝ
  locality : ℝ
  maxlink : ℝ
  max_acc : ℝ
  nocoda : ℝ
  nonfinal : ℝ
  osd : ℝ
  rightmost : ℝ
  sync : ℝ
def nonnegative (w : Weights) : Prop :=
  0 ≤ w.clash ∧ 0 ≤ w.dep ∧ 0 ≤ w.deplink ∧ 0 ≤ w.dep_acc ∧ 0 ≤ w.dock_prev ∧ 0 ≤ w.float ∧ 0 ≤ w.locality ∧ 0 ≤ w.maxlink ∧ 0 ≤ w.max_acc ∧ 0 ≤ w.nocoda ∧ 0 ≤ w.nonfinal ∧ 0 ≤ w.osd ∧ 0 ≤ w.rightmost ∧ 0 ≤ w.sync
def bigfish_0 (w : Weights) (l : ℝ) : Prop :=
  0 < ((2 * w.max_acc) + (w.nonfinal * l) + ((-2) * w.float * l)) ∧
  0 < ((2 * w.max_acc) + (w.osd * l) + (w.rightmost * l) + ((-2) * w.float * l)) ∧
  0 < (w.max_acc + ((-1) * w.maxlink) + (w.rightmost * l) + ((-2) * w.float * l)) ∧
  0 < (((-1) * w.deplink) + ((-1) * w.dep_acc) + (w.osd * l)) ∧
  0 < (((-1) * w.deplink) + ((-1) * w.dep_acc) + (2 * w.max_acc) + (w.osd * l) + ((-2) * w.float * l)) ∧
  0 < (w.max_acc + ((-1) * w.deplink) + ((-1) * w.dep_acc) + (w.osd * l) + ((-1) * w.float * l)) ∧
  0 < (w.max_acc + ((-1) * w.dep_acc) + (w.locality * l) + (w.nonfinal * l) + ((-2) * w.float * l)) ∧
  0 < (w.max_acc + ((-1) * w.dep_acc) + (w.locality * l) + (w.osd * l) + (w.rightmost * l) + ((-2) * w.float * l)) ∧
  0 < (w.max_acc + ((-1) * w.dep_acc) + (w.nonfinal * l) + ((-2) * w.float * l)) ∧
  0 < (w.max_acc + ((-1) * w.dep_acc) + (w.osd * l) + (w.rightmost * l) + ((-2) * w.float * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.maxlink) + (w.rightmost * l) + ((-2) * w.float * l)) ∧
  0 < (((-1) * w.dep_acc) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.dep_acc) + (w.locality * l) + (w.osd * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.dep_acc) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.dep_acc) + (w.osd * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.max_acc + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.max_acc + (w.osd * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.maxlink) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < w.clash ∧
  0 < (w.clash + w.deplink + w.max_acc + (w.locality * l) + ((-2) * w.float * l)) ∧
  0 < (w.clash + w.deplink + w.max_acc + (w.locality * l) + (w.nonfinal * l) + ((-2) * w.float * l)) ∧
  0 < (w.clash + w.deplink + w.max_acc + (w.nonfinal * l) + ((-2) * w.float * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.dep_acc) + ((-2) * w.float * l) + (2 * w.locality * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.dep_acc) + (w.nonfinal * l) + ((-2) * w.float * l) + (2 * w.locality * l)) ∧
  0 < (w.clash + w.deplink + (w.locality * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + (2 * w.max_acc) + ((-2) * w.float * l)) ∧
  0 < (w.clash + w.max_acc + ((-1) * w.maxlink) + ((-2) * w.float * l)) ∧
  0 < (w.clash + w.max_acc + ((-1) * w.maxlink) + (w.nonfinal * l) + ((-2) * w.float * l)) ∧
  0 < (w.clash + ((-1) * w.deplink) + ((-1) * w.dep_acc) + ((-2) * w.maxlink) + ((-2) * w.float * l)) ∧
  0 < (w.clash + w.max_acc + ((-1) * w.deplink) + ((-1) * w.dep_acc) + ((-1) * w.maxlink) + ((-2) * w.float * l)) ∧
  0 < (w.clash + ((-1) * w.deplink) + ((-1) * w.dep_acc) + ((-1) * w.maxlink) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.max_acc + ((-1) * w.dep_acc) + (w.locality * l) + ((-2) * w.float * l)) ∧
  0 < (w.clash + ((-1) * w.dep_acc) + ((-1) * w.maxlink) + (w.nonfinal * l) + ((-2) * w.float * l)) ∧
  0 < (w.clash + ((-1) * w.dep_acc) + (w.locality * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.max_acc + ((-1) * w.float * l)) ∧
  0 < (w.clash + ((-1) * w.maxlink) + ((-1) * w.float * l)) ∧
  0 < (w.clash + ((-1) * w.maxlink) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < ((2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-2) * w.float * l) + (2 * w.locality * l)) ∧
  0 < ((2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-2) * w.float * l)) ∧
  0 < ((2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-2) * w.float * l)) ∧
  0 < (w.clash + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + ((-2) * w.float * l) + (2 * w.locality * l)) ∧
  0 < (w.clash + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-2) * w.float * l) + (2 * w.locality * l)) ∧
  0 < (w.clash + (2 * w.deplink) + (w.clash * l) + (w.rightmost * l) + ((-2) * w.float * l) + (2 * w.locality * l)) ∧
  0 < (w.clash + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + ((-2) * w.float * l)) ∧
  0 < (w.clash + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-2) * w.float * l)) ∧
  0 < (w.clash + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.rightmost * l) + ((-2) * w.float * l)) ∧
  0 < (w.clash + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-2) * w.float * l)) ∧
  0 < (w.clash + w.deplink + w.max_acc + (w.clash * l) + (w.locality * l) + (w.rightmost * l) + ((-2) * w.float * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.maxlink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + ((-2) * w.float * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.maxlink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-2) * w.float * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.maxlink) + (w.clash * l) + (w.locality * l) + (w.rightmost * l) + ((-2) * w.float * l)) ∧
  0 < (w.clash + w.deplink + w.max_acc + (w.clash * l) + (w.rightmost * l) + ((-2) * w.float * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.maxlink) + (w.clash * l) + (w.nonfinal * l) + ((-2) * w.float * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.maxlink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-2) * w.float * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.maxlink) + (w.clash * l) + (w.rightmost * l) + ((-2) * w.float * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.dep_acc) + (w.clash * l) + (w.locality * l) + (w.rightmost * l) + ((-2) * w.float * l)) ∧
  0 < (w.clash + w.deplink + (w.clash * l) + (w.locality * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + (w.clash * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + ((-2) * w.maxlink) + (w.clash * l) + (w.nonfinal * l) + ((-2) * w.float * l)) ∧
  0 < (w.clash + ((-2) * w.maxlink) + (w.clash * l) + (w.rightmost * l) + ((-2) * w.float * l)) ∧
  0 < (w.clash + w.max_acc + ((-1) * w.maxlink) + (w.clash * l) + (w.rightmost * l) + ((-2) * w.float * l)) ∧
  0 < (w.clash + ((-1) * w.dep_acc) + ((-1) * w.maxlink) + (w.clash * l) + (w.locality * l) + (w.rightmost * l) + ((-2) * w.float * l)) ∧
  0 < (w.clash + ((-1) * w.maxlink) + (w.clash * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.max_acc + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + ((-2) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.maxlink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-2) * w.float * l)) ∧
  0 < (w.deplink + w.max_acc + (w.clash * l) + (w.nonfinal * l) + ((-2) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.maxlink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-2) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + ((-2) * w.float * l)) ∧
  0 < (w.deplink + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.max_acc + ((-1) * w.maxlink) + (w.clash * l) + (w.nonfinal * l) + ((-2) * w.float * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.maxlink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + ((-2) * w.float * l)) ∧
  0 < (((-1) * w.maxlink) + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.max_acc + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-2) * w.float * l)) ∧
  0 < (w.deplink + w.max_acc + (w.locality * l) + (w.rightmost * l) + ((-2) * w.float * l)) ∧
  0 < (w.deplink + w.max_acc + (w.nonfinal * l) + (w.rightmost * l) + ((-2) * w.float * l)) ∧
  0 < (w.deplink + w.max_acc + (w.rightmost * l) + ((-2) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + (w.nonfinal * l) + (w.rightmost * l) + ((-2) * w.float * l) + (2 * w.locality * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + (w.rightmost * l) + ((-2) * w.float * l) + (2 * w.locality * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + (w.nonfinal * l) + (w.rightmost * l) + ((-2) * w.float * l)) ∧
  0 < (w.deplink + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.locality * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.nonfinal * l) ∧
  0 < ((w.osd * l) + (w.rightmost * l))
def bigfish_1 (w : Weights) (l : ℝ) : Prop :=
  0 < (((-1) * w.deplink) + ((-1) * w.max_acc) + (w.osd * l) + ((-1) * w.locality * l) + (2 * w.float * l)) ∧
  0 < (((-1) * w.deplink) + (w.float * l) + (w.osd * l) + ((-1) * w.locality * l)) ∧
  0 < (w.max_acc + ((-1) * w.deplink) + (w.osd * l) + ((-1) * w.locality * l)) ∧
  0 < (((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < w.clash ∧
  0 < (w.clash + w.deplink + w.dep_acc) ∧
  0 < (w.clash + w.deplink + w.dep_acc + ((-1) * w.max_acc) + (w.float * l) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + ((-1) * w.max_acc) + (w.float * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + ((-1) * w.max_acc) + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + (w.nonfinal * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.max_acc) + (w.locality * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.max_acc) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.clash + w.dep_acc + ((-1) * w.max_acc) + ((-1) * w.locality * l) + (2 * w.float * l)) ∧
  0 < (w.clash + w.dep_acc + (w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.float * l) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + w.max_acc + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + ((-1) * w.maxlink) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + ((-1) * w.maxlink) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + ((-1) * w.max_acc) + (w.float * l)) ∧
  0 < (w.clash + ((-1) * w.deplink) + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + ((-1) * w.deplink) + ((-1) * w.max_acc) + ((-2) * w.maxlink) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + ((-1) * w.deplink) + ((-1) * w.maxlink) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.dep_acc + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.clash + w.dep_acc + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.clash + w.dep_acc + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.clash + w.dep_acc + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.rightmost * l)) ∧
  0 < (w.clash + w.dep_acc + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (w.clash + w.dep_acc + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.clash + w.dep_acc + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.rightmost * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + ((-1) * w.max_acc) + (w.clash * l) + (w.float * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + ((-1) * w.max_acc) + (w.clash * l) + (w.float * l) + (w.rightmost * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + (w.clash * l) + (w.rightmost * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + (w.clash * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + (w.rightmost * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.max_acc) + (w.clash * l) + (w.rightmost * l)) ∧
  0 < (w.clash + w.dep_acc + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + (w.float * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + ((-1) * w.max_acc) + ((-2) * w.maxlink) + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + ((-1) * w.max_acc) + ((-2) * w.maxlink) + (w.clash * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + ((-1) * w.maxlink) + (w.clash * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.max_acc) + (w.clash * l) + (w.float * l) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.max_acc) + (w.clash * l) + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (w.dep_acc + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + (w.float * l) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + ((-1) * w.maxlink) + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.max_acc) + (w.float * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.max_acc) + (w.float * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.max_acc) + (w.float * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.max_acc) + (w.float * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.locality * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + ((-1) * w.max_acc) + (w.nonfinal * l) + ((-1) * w.locality * l) + (2 * w.float * l)) ∧
  0 < (w.dep_acc + ((-1) * w.max_acc) + (w.osd * l) + (w.rightmost * l) + ((-1) * w.locality * l) + (2 * w.float * l)) ∧
  0 < (w.dep_acc + (w.float * l) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + (w.float * l) + (w.osd * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.float * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + w.max_acc + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + w.max_acc + (w.osd * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + ((-1) * w.maxlink) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (((-1) * w.max_acc) + (w.float * l) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (((-1) * w.max_acc) + (w.float * l) + (w.osd * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (((-1) * w.max_acc) + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (((-1) * w.max_acc) + (w.float * l) + (w.osd * l) + (w.rightmost * l)) ∧
  0 < (w.nonfinal * l) ∧
  0 < ((w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < ((w.osd * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < ((w.osd * l) + (w.rightmost * l))
def bigfish_2 (w : Weights) (l : ℝ) : Prop :=
  0 < (((-1) * w.deplink) + (w.float * l) + (w.osd * l) + ((-1) * w.locality * l)) ∧
  0 < (((-1) * w.deplink) + (2 * w.max_acc) + (w.osd * l) + ((-1) * w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.max_acc + ((-1) * w.deplink) + (w.osd * l) + ((-1) * w.locality * l)) ∧
  0 < (w.max_acc + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.max_acc + (w.osd * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.max_acc + (w.nonfinal * l) + ((-1) * w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.max_acc + (w.osd * l) + (w.rightmost * l) + ((-1) * w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (((-1) * w.maxlink) + (w.rightmost * l) + ((-1) * w.float * l) + ((-1) * w.locality * l)) ∧
  0 < w.clash ∧
  0 < (w.clash + w.deplink + w.dep_acc) ∧
  0 < (w.clash + w.deplink + w.dep_acc + (w.nonfinal * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + w.max_acc + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + w.max_acc + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + w.max_acc + (w.nonfinal * l) + ((-1) * w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.deplink + (w.locality * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.dep_acc + (w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + (2 * w.max_acc) + ((-1) * w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + w.max_acc + ((-1) * w.maxlink) + ((-1) * w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + w.max_acc + ((-1) * w.maxlink) + (w.nonfinal * l) + ((-1) * w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + w.max_acc + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + ((-1) * w.maxlink) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + ((-1) * w.maxlink) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + ((-1) * w.deplink) + ((-2) * w.maxlink) + ((-1) * w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.max_acc + ((-1) * w.deplink) + ((-1) * w.maxlink) + ((-1) * w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + ((-1) * w.deplink) + ((-1) * w.maxlink) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.max_acc + ((-1) * w.float * l)) ∧
  0 < (w.clash + ((-1) * w.maxlink) + (w.nonfinal * l) + ((-1) * w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.dep_acc + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.dep_acc + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.dep_acc + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.dep_acc + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.dep_acc + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.dep_acc + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.dep_acc + (2 * w.deplink) + (w.clash * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.dep_acc + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + (w.clash * l) + (w.rightmost * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + w.max_acc + (w.clash * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + w.max_acc + (w.clash * l) + (w.rightmost * l) + ((-1) * w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + ((-1) * w.maxlink) + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + ((-1) * w.maxlink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + ((-1) * w.maxlink) + (w.clash * l) + (w.rightmost * l) + ((-1) * w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + ((-1) * w.maxlink) + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + ((-1) * w.maxlink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + ((-1) * w.maxlink) + (w.clash * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + (w.clash * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.deplink + (w.clash * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.dep_acc + ((-2) * w.maxlink) + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + ((-2) * w.maxlink) + (w.clash * l) + (w.rightmost * l) + ((-1) * w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + w.max_acc + ((-1) * w.maxlink) + (w.clash * l) + (w.rightmost * l) + ((-1) * w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + ((-1) * w.maxlink) + (w.clash * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + ((-1) * w.maxlink) + (w.clash * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dep_acc + w.max_acc + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.dep_acc + w.max_acc + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.maxlink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.maxlink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.dep_acc + w.max_acc + ((-1) * w.maxlink) + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + ((-1) * w.maxlink) + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (((-1) * w.maxlink) + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dep_acc + w.max_acc + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.dep_acc + w.max_acc + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.dep_acc + w.max_acc + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + w.max_acc + (w.rightmost * l) + ((-1) * w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.locality * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + (w.float * l) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + (w.float * l) + (w.osd * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + (2 * w.max_acc) + (w.nonfinal * l) + ((-1) * w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + (2 * w.max_acc) + (w.osd * l) + (w.rightmost * l) + ((-1) * w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + w.max_acc + ((-1) * w.maxlink) + (w.rightmost * l) + ((-1) * w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + w.max_acc + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + w.max_acc + (w.osd * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + ((-1) * w.maxlink) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.nonfinal * l) ∧
  0 < ((w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < ((w.osd * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < ((w.osd * l) + (w.rightmost * l))
def bigfish_3 (w : Weights) (l : ℝ) : Prop :=
  0 < (((-1) * w.deplink) + ((-1) * w.dep_acc) + ((-2) * w.max_acc) + (w.osd * l) + (2 * w.float * l)) ∧
  0 < (((-1) * w.deplink) + ((-1) * w.dep_acc) + ((-1) * w.max_acc) + (w.float * l) + (w.osd * l)) ∧
  0 < (((-1) * w.deplink) + ((-1) * w.dep_acc) + (w.osd * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-2) * w.max_acc) + (w.float * l) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-2) * w.max_acc) + (w.float * l) + (w.locality * l) + (w.osd * l) + (w.rightmost * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-2) * w.max_acc) + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-2) * w.max_acc) + (w.float * l) + (w.osd * l) + (w.rightmost * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.max_acc) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.max_acc) + (w.locality * l) + (w.osd * l) + (w.rightmost * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.maxlink) + ((-2) * w.max_acc) + (w.rightmost * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.max_acc) + (w.nonfinal * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.max_acc) + (w.osd * l) + (w.rightmost * l)) ∧
  0 < (((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.rightmost * l)) ∧
  0 < (((-2) * w.max_acc) + (w.nonfinal * l) + (2 * w.float * l)) ∧
  0 < (((-2) * w.max_acc) + (w.osd * l) + (w.rightmost * l) + (2 * w.float * l)) ∧
  0 < w.clash ∧
  0 < (w.clash + ((-2) * w.max_acc) + (2 * w.float * l)) ∧
  0 < (w.clash + w.deplink + ((-2) * w.max_acc) + (w.float * l) + (w.locality * l)) ∧
  0 < (w.clash + w.deplink + ((-2) * w.max_acc) + (w.float * l) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.clash + w.deplink + ((-2) * w.max_acc) + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.max_acc) + (w.locality * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.max_acc) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.dep_acc) + ((-2) * w.max_acc) + (2 * w.locality * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.dep_acc) + ((-2) * w.max_acc) + (w.nonfinal * l) + (2 * w.locality * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.max_acc) + (w.nonfinal * l)) ∧
  0 < (w.clash + ((-1) * w.maxlink) + ((-2) * w.max_acc) + (w.float * l)) ∧
  0 < (w.clash + ((-1) * w.maxlink) + ((-2) * w.max_acc) + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (w.clash + ((-1) * w.max_acc) + (w.float * l)) ∧
  0 < (w.clash + ((-1) * w.deplink) + ((-1) * w.dep_acc) + ((-1) * w.maxlink) + ((-2) * w.max_acc) + (w.float * l)) ∧
  0 < (w.clash + ((-1) * w.deplink) + ((-1) * w.dep_acc) + ((-2) * w.maxlink) + ((-2) * w.max_acc)) ∧
  0 < (w.clash + ((-1) * w.deplink) + ((-1) * w.dep_acc) + ((-1) * w.maxlink) + ((-1) * w.max_acc)) ∧
  0 < (w.clash + ((-1) * w.dep_acc) + ((-2) * w.max_acc) + (w.float * l) + (w.locality * l)) ∧
  0 < (w.clash + ((-1) * w.dep_acc) + ((-1) * w.max_acc) + (w.locality * l)) ∧
  0 < (w.clash + ((-1) * w.dep_acc) + ((-1) * w.maxlink) + ((-2) * w.max_acc) + (w.nonfinal * l)) ∧
  0 < (w.clash + ((-1) * w.maxlink) + ((-1) * w.max_acc)) ∧
  0 < (w.clash + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.nonfinal * l)) ∧
  0 < (((-2) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l) + (2 * w.locality * l)) ∧
  0 < (((-2) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (((-2) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.clash + ((-2) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (2 * w.locality * l)) ∧
  0 < (w.clash + ((-2) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l) + (2 * w.locality * l)) ∧
  0 < (w.clash + ((-2) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.rightmost * l) + (2 * w.locality * l)) ∧
  0 < (w.clash + ((-2) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.clash + ((-2) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.clash + ((-2) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.rightmost * l)) ∧
  0 < (w.clash + ((-2) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.clash + w.deplink + ((-2) * w.max_acc) + (w.clash * l) + (w.float * l) + (w.locality * l) + (w.rightmost * l)) ∧
  0 < (w.clash + w.deplink + ((-2) * w.max_acc) + (w.clash * l) + (w.float * l) + (w.rightmost * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.maxlink) + ((-2) * w.max_acc) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.maxlink) + ((-2) * w.max_acc) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.maxlink) + ((-2) * w.max_acc) + (w.clash * l) + (w.locality * l) + (w.rightmost * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.max_acc) + (w.clash * l) + (w.locality * l) + (w.rightmost * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.dep_acc) + ((-2) * w.max_acc) + (w.clash * l) + (w.locality * l) + (w.rightmost * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.maxlink) + ((-2) * w.max_acc) + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.maxlink) + ((-2) * w.max_acc) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.maxlink) + ((-2) * w.max_acc) + (w.clash * l) + (w.rightmost * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.max_acc) + (w.clash * l) + (w.rightmost * l)) ∧
  0 < (w.clash + ((-1) * w.maxlink) + ((-2) * w.max_acc) + (w.clash * l) + (w.float * l) + (w.rightmost * l)) ∧
  0 < (w.clash + ((-2) * w.maxlink) + ((-2) * w.max_acc) + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (w.clash + ((-2) * w.maxlink) + ((-2) * w.max_acc) + (w.clash * l) + (w.rightmost * l)) ∧
  0 < (w.clash + ((-1) * w.dep_acc) + ((-1) * w.maxlink) + ((-2) * w.max_acc) + (w.clash * l) + (w.locality * l) + (w.rightmost * l)) ∧
  0 < (w.clash + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-2) * w.max_acc) + (w.clash * l) + (w.float * l) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-2) * w.max_acc) + (w.clash * l) + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-1) * w.maxlink) + ((-2) * w.max_acc) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + ((-2) * w.max_acc) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-1) * w.maxlink) + ((-2) * w.max_acc) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (((-1) * w.maxlink) + ((-2) * w.max_acc) + (w.clash * l) + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.maxlink) + ((-2) * w.max_acc) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-2) * w.max_acc) + (w.float * l) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-2) * w.max_acc) + (w.float * l) + (w.locality * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-2) * w.max_acc) + (w.float * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-2) * w.max_acc) + (w.float * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.locality * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + ((-2) * w.max_acc) + (w.nonfinal * l) + (w.rightmost * l) + (2 * w.locality * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + ((-2) * w.max_acc) + (w.rightmost * l) + (2 * w.locality * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + ((-2) * w.max_acc) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.rightmost * l)) ∧
  0 < (((-1) * w.maxlink) + ((-2) * w.max_acc) + (w.float * l) + (w.rightmost * l)) ∧
  0 < (((-1) * w.max_acc) + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (((-1) * w.max_acc) + (w.float * l) + (w.osd * l) + (w.rightmost * l)) ∧
  0 < (w.nonfinal * l) ∧
  0 < ((w.osd * l) + (w.rightmost * l))
def bigfish_4 (w : Weights) (l : ℝ) : Prop :=
  0 < (((-1) * w.deplink) + ((-1) * w.dep_acc) + ((-1) * w.max_acc) + (w.float * l) + (w.osd * l)) ∧
  0 < (((-1) * w.deplink) + ((-1) * w.dep_acc) + (w.osd * l)) ∧
  0 < (w.max_acc + ((-1) * w.deplink) + ((-1) * w.dep_acc) + (w.osd * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.max_acc) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.max_acc) + (w.locality * l) + (w.osd * l) + (w.rightmost * l)) ∧
  0 < (((-1) * w.dep_acc) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.dep_acc) + (w.locality * l) + (w.osd * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.dep_acc) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.dep_acc) + (w.osd * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.max_acc) + (w.nonfinal * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.max_acc) + (w.osd * l) + (w.rightmost * l)) ∧
  0 < (w.max_acc + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.max_acc + (w.osd * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.maxlink) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.rightmost * l)) ∧
  0 < w.clash ∧
  0 < (w.clash + w.deplink + ((-1) * w.max_acc) + (w.locality * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.max_acc) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.dep_acc) + ((-1) * w.max_acc) + ((-1) * w.float * l) + (2 * w.locality * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.dep_acc) + ((-1) * w.max_acc) + (w.nonfinal * l) + ((-1) * w.float * l) + (2 * w.locality * l)) ∧
  0 < (w.clash + w.deplink + (w.locality * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.max_acc) + (w.nonfinal * l)) ∧
  0 < (w.clash + ((-1) * w.max_acc) + (w.float * l)) ∧
  0 < (w.clash + ((-1) * w.deplink) + ((-1) * w.dep_acc) + ((-1) * w.max_acc) + ((-2) * w.maxlink) + ((-1) * w.float * l)) ∧
  0 < (w.clash + ((-1) * w.deplink) + ((-1) * w.dep_acc) + ((-1) * w.maxlink) + ((-1) * w.float * l)) ∧
  0 < (w.clash + ((-1) * w.deplink) + ((-1) * w.dep_acc) + ((-1) * w.maxlink) + ((-1) * w.max_acc)) ∧
  0 < (w.clash + ((-1) * w.dep_acc) + ((-1) * w.max_acc) + (w.locality * l)) ∧
  0 < (w.clash + ((-1) * w.dep_acc) + (w.locality * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + ((-1) * w.dep_acc) + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.max_acc + ((-1) * w.float * l)) ∧
  0 < (w.clash + ((-1) * w.maxlink) + ((-1) * w.float * l)) ∧
  0 < (w.clash + ((-1) * w.maxlink) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + ((-1) * w.maxlink) + ((-1) * w.max_acc)) ∧
  0 < (w.clash + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.nonfinal * l)) ∧
  0 < (((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l) + (2 * w.locality * l)) ∧
  0 < (((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.float * l) + (2 * w.locality * l)) ∧
  0 < (w.clash + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l) + (2 * w.locality * l)) ∧
  0 < (w.clash + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.rightmost * l) + ((-1) * w.float * l) + (2 * w.locality * l)) ∧
  0 < (w.clash + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.max_acc) + (w.clash * l) + (w.locality * l) + (w.rightmost * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.dep_acc) + ((-1) * w.max_acc) + (w.clash * l) + (w.locality * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + (w.clash * l) + (w.locality * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + (w.locality * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + (w.clash * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.max_acc) + (w.clash * l) + (w.rightmost * l)) ∧
  0 < (w.clash + ((-1) * w.dep_acc) + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + (w.locality * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + ((-1) * w.max_acc) + ((-2) * w.maxlink) + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + ((-1) * w.max_acc) + ((-2) * w.maxlink) + (w.clash * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + ((-1) * w.maxlink) + (w.clash * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + ((-1) * w.max_acc) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.maxlink) + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.locality * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + ((-1) * w.max_acc) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l) + (2 * w.locality * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + ((-1) * w.max_acc) + (w.rightmost * l) + ((-1) * w.float * l) + (2 * w.locality * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + ((-1) * w.max_acc) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.locality * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.rightmost * l)) ∧
  0 < (((-1) * w.max_acc) + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (((-1) * w.max_acc) + (w.float * l) + (w.osd * l) + (w.rightmost * l)) ∧
  0 < (w.nonfinal * l) ∧
  0 < ((w.osd * l) + (w.rightmost * l))
def bigfish_5 (w : Weights) (l : ℝ) : Prop :=
  0 < (w.maxlink + (2 * w.max_acc) + (w.osd * l) + ((-1) * w.float * l)) ∧
  0 < (w.dep_acc + w.maxlink + (2 * w.deplink) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.dep_acc + w.maxlink + (2 * w.deplink) + (w.locality * l) + (w.rightmost * l)) ∧
  0 < (w.dep_acc + w.maxlink + (2 * w.deplink) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.dep_acc + w.maxlink + (2 * w.deplink) + (w.rightmost * l)) ∧
  0 < (w.dep_acc + w.maxlink + w.max_acc + (2 * w.deplink) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.dep_acc + w.maxlink + w.max_acc + (2 * w.deplink) + (w.locality * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.dep_acc + w.maxlink + w.max_acc + (2 * w.deplink) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.dep_acc + w.maxlink + w.max_acc + (2 * w.deplink) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.maxlink + (2 * w.deplink) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l) + (2 * w.locality * l)) ∧
  0 < (w.maxlink + (2 * w.deplink) + (w.rightmost * l) + ((-1) * w.float * l) + (2 * w.locality * l)) ∧
  0 < (w.maxlink + (2 * w.deplink) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < w.clash ∧
  0 < (w.clash + w.dep_acc + w.maxlink + (2 * w.deplink) + (w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + (2 * w.deplink) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + (2 * w.deplink) + (w.nonfinal * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + w.max_acc + (2 * w.deplink) + (w.locality * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + w.max_acc + (2 * w.deplink) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + w.max_acc + (2 * w.deplink) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.maxlink + (2 * w.deplink) + ((-1) * w.float * l) + (2 * w.locality * l)) ∧
  0 < (w.clash + w.maxlink + (2 * w.deplink) + (w.nonfinal * l) + ((-1) * w.float * l) + (2 * w.locality * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc) ∧
  0 < (w.clash + w.deplink + w.dep_acc + w.maxlink + (w.float * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + w.maxlink + w.max_acc) ∧
  0 < (w.clash + w.deplink + w.dep_acc + (w.nonfinal * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + w.maxlink + (2 * w.max_acc) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + w.max_acc + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + w.max_acc + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + w.maxlink + (w.locality * l)) ∧
  0 < (w.clash + w.deplink + w.maxlink + w.max_acc + (w.locality * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.max_acc + ((-1) * w.float * l)) ∧
  0 < (w.clash + ((-1) * w.maxlink) + ((-1) * w.float * l)) ∧
  0 < (w.dep_acc + w.maxlink + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.dep_acc + w.maxlink + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (w.dep_acc + w.maxlink + w.max_acc + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.dep_acc + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.dep_acc + w.maxlink + w.max_acc + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.dep_acc + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.maxlink + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.dep_acc + w.maxlink + (3 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l) + (2 * w.locality * l)) ∧
  0 < (w.dep_acc + w.maxlink + (3 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.dep_acc + w.maxlink + (3 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.rightmost * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + (2 * w.deplink) + (w.clash * l) + (w.rightmost * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + w.max_acc + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.dep_acc + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.dep_acc + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.dep_acc + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + w.max_acc + (2 * w.deplink) + (w.clash * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.dep_acc + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.dep_acc + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.dep_acc + (2 * w.deplink) + (w.clash * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.maxlink + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + (3 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.float * l) + (2 * w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + (3 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l) + (2 * w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + (3 * w.deplink) + (w.clash * l) + (w.rightmost * l) + ((-1) * w.float * l) + (2 * w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + (3 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + (3 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + (3 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + (3 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + (w.clash * l) + (w.rightmost * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + w.max_acc + (w.clash * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + ((-1) * w.maxlink) + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + ((-1) * w.maxlink) + (w.clash * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + (w.clash * l) + (w.locality * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dep_acc + w.max_acc + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.dep_acc + w.maxlink + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dep_acc + w.maxlink + (w.float * l) + (w.osd * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dep_acc + w.maxlink + w.max_acc + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dep_acc + w.maxlink + w.max_acc + (w.osd * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dep_acc + w.maxlink + (2 * w.max_acc) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.dep_acc + w.maxlink + (2 * w.max_acc) + (w.osd * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.dep_acc + w.max_acc + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.maxlink + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.maxlink + (w.locality * l) + (w.osd * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.maxlink + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.maxlink + (w.osd * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.maxlink + w.max_acc + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.maxlink + w.max_acc + (w.locality * l) + (w.osd * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.maxlink + w.max_acc + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.maxlink + w.max_acc + (w.osd * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.maxlink + (w.float * l) + (w.osd * l)) ∧
  0 < (w.maxlink + w.max_acc + (w.osd * l))
def bigfish_6 (w : Weights) (l : ℝ) : Prop :=
  0 < (w.maxlink + ((-1) * w.max_acc) + (2 * w.deplink) + (w.nonfinal * l) + (w.rightmost * l) + (2 * w.locality * l)) ∧
  0 < (w.maxlink + ((-1) * w.max_acc) + (2 * w.deplink) + (w.rightmost * l) + (2 * w.locality * l)) ∧
  0 < (w.dep_acc + w.maxlink + ((-1) * w.max_acc) + (2 * w.deplink) + (w.float * l) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.dep_acc + w.maxlink + ((-1) * w.max_acc) + (2 * w.deplink) + (w.float * l) + (w.locality * l) + (w.rightmost * l)) ∧
  0 < (w.dep_acc + w.maxlink + ((-1) * w.max_acc) + (2 * w.deplink) + (w.float * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.dep_acc + w.maxlink + ((-1) * w.max_acc) + (2 * w.deplink) + (w.float * l) + (w.rightmost * l)) ∧
  0 < (w.dep_acc + w.maxlink + (2 * w.deplink) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.dep_acc + w.maxlink + (2 * w.deplink) + (w.locality * l) + (w.rightmost * l)) ∧
  0 < (w.dep_acc + w.maxlink + (2 * w.deplink) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.dep_acc + w.maxlink + (2 * w.deplink) + (w.rightmost * l)) ∧
  0 < (w.maxlink + ((-1) * w.max_acc) + (2 * w.deplink) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.maxlink + ((-1) * w.max_acc) + (w.osd * l) + (2 * w.float * l)) ∧
  0 < w.clash ∧
  0 < (w.clash + w.maxlink + ((-1) * w.max_acc) + (2 * w.deplink) + (2 * w.locality * l)) ∧
  0 < (w.clash + w.maxlink + ((-1) * w.max_acc) + (2 * w.deplink) + (w.nonfinal * l) + (2 * w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + ((-1) * w.max_acc) + (2 * w.deplink) + (w.float * l) + (w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + ((-1) * w.max_acc) + (2 * w.deplink) + (w.float * l) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + ((-1) * w.max_acc) + (2 * w.deplink) + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + (2 * w.deplink) + (w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + (2 * w.deplink) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + (2 * w.deplink) + (w.nonfinal * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc) ∧
  0 < (w.clash + w.deplink + w.dep_acc + w.maxlink + ((-1) * w.max_acc) + (2 * w.float * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + w.maxlink + (w.float * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + ((-1) * w.max_acc) + (w.float * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + ((-1) * w.max_acc) + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + w.maxlink + w.max_acc) ∧
  0 < (w.clash + w.deplink + w.dep_acc + (w.nonfinal * l)) ∧
  0 < (w.clash + w.deplink + w.maxlink + ((-1) * w.max_acc) + (w.float * l) + (w.locality * l)) ∧
  0 < (w.clash + w.deplink + w.maxlink + (w.locality * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.max_acc) + (w.nonfinal * l)) ∧
  0 < (w.clash + ((-1) * w.max_acc) + (w.float * l)) ∧
  0 < (w.clash + ((-1) * w.maxlink) + ((-1) * w.max_acc)) ∧
  0 < (w.dep_acc + w.maxlink + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.float * l) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.dep_acc + w.maxlink + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (w.dep_acc + w.maxlink + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.dep_acc + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.dep_acc + w.maxlink + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (w.dep_acc + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.maxlink + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.dep_acc + w.maxlink + ((-1) * w.max_acc) + (3 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l) + (2 * w.locality * l)) ∧
  0 < (w.dep_acc + w.maxlink + ((-1) * w.max_acc) + (3 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.dep_acc + w.maxlink + ((-1) * w.max_acc) + (3 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.float * l) + (w.locality * l) + (w.rightmost * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.float * l) + (w.rightmost * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.rightmost * l)) ∧
  0 < (w.clash + w.dep_acc + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.clash + w.dep_acc + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.clash + w.dep_acc + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.rightmost * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + (2 * w.deplink) + (w.clash * l) + (w.rightmost * l)) ∧
  0 < (w.clash + w.dep_acc + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (w.clash + w.dep_acc + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.clash + w.dep_acc + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.rightmost * l)) ∧
  0 < (w.clash + w.maxlink + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.rightmost * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + ((-1) * w.max_acc) + (3 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (2 * w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + ((-1) * w.max_acc) + (3 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l) + (2 * w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + ((-1) * w.max_acc) + (3 * w.deplink) + (w.clash * l) + (w.rightmost * l) + (2 * w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + ((-1) * w.max_acc) + (3 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + ((-1) * w.max_acc) + (3 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + ((-1) * w.max_acc) + (3 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.rightmost * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + ((-1) * w.max_acc) + (3 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + ((-1) * w.max_acc) + (w.clash * l) + (w.float * l) + (w.rightmost * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + (w.clash * l) + (w.rightmost * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + (w.rightmost * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.max_acc) + (w.clash * l) + (w.locality * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.max_acc) + (w.clash * l) + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dep_acc + w.maxlink + ((-1) * w.max_acc) + (w.nonfinal * l) + (2 * w.float * l)) ∧
  0 < (w.deplink + w.dep_acc + w.maxlink + ((-1) * w.max_acc) + (w.osd * l) + (w.rightmost * l) + (2 * w.float * l)) ∧
  0 < (w.deplink + w.dep_acc + w.maxlink + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dep_acc + w.maxlink + (w.float * l) + (w.osd * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.max_acc) + (w.float * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dep_acc + w.maxlink + w.max_acc + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dep_acc + w.maxlink + w.max_acc + (w.osd * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.rightmost * l)) ∧
  0 < (w.deplink + w.maxlink + ((-1) * w.max_acc) + (w.float * l) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.maxlink + ((-1) * w.max_acc) + (w.float * l) + (w.locality * l) + (w.osd * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.maxlink + ((-1) * w.max_acc) + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.maxlink + ((-1) * w.max_acc) + (w.float * l) + (w.osd * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.maxlink + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.maxlink + (w.locality * l) + (w.osd * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.maxlink + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.maxlink + (w.osd * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.rightmost * l)) ∧
  0 < (w.maxlink + (w.float * l) + (w.osd * l)) ∧
  0 < (w.maxlink + w.max_acc + (w.osd * l))
def bigfish (w : Weights) (l : ℝ) : Prop :=
  bigfish_0 w l ∨ bigfish_1 w l ∨ bigfish_2 w l ∨ bigfish_3 w l ∨ bigfish_4 w l ∨ bigfish_5 w l ∨ bigfish_6 w l
def bull_pl_0 (w : Weights) (l : ℝ) : Prop :=
  0 < (((-1) * w.deplink) + ((-1) * w.dep_acc) + ((-1) * w.max_acc) + (w.float * l) + (w.osd * l)) ∧
  0 < (((-1) * w.deplink) + ((-1) * w.dep_acc) + (w.osd * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.max_acc) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.max_acc)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.max_acc) + (w.osd * l) + (w.rightmost * l)) ∧
  0 < (((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.nonfinal * l)) ∧
  0 < 0 ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.clash * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.clash * l) + (w.rightmost * l)) ∧
  0 < (((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l)) ∧
  0 < (((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.rightmost * l)) ∧
  0 < (((-1) * w.max_acc) + (w.float * l)) ∧
  0 < (((-1) * w.max_acc) + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (((-1) * w.max_acc) + (w.float * l) + (w.osd * l) + (w.rightmost * l)) ∧
  0 < (w.nonfinal * l) ∧
  0 < ((w.osd * l) + (w.rightmost * l))
def bull_pl_1 (w : Weights) (l : ℝ) : Prop :=
  0 < (((-1) * w.deplink) + ((-1) * w.dep_acc) + (w.osd * l)) ∧
  0 < (w.max_acc + ((-1) * w.deplink) + ((-1) * w.dep_acc) + (w.osd * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.dep_acc) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.dep_acc) + (w.osd * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.max_acc + ((-1) * w.float * l)) ∧
  0 < (w.max_acc + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.max_acc + (w.osd * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.maxlink) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < 0 ∧
  0 < (w.deplink + (w.clash * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.clash * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.maxlink) + (w.clash * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.maxlink) + (w.clash * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.nonfinal * l) ∧
  0 < ((w.osd * l) + (w.rightmost * l))
def bull_pl_2 (w : Weights) (l : ℝ) : Prop :=
  0 < (w.dep_acc + w.maxlink + (2 * w.deplink) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.dep_acc + w.maxlink + (2 * w.deplink) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.dep_acc + w.maxlink + (2 * w.deplink) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.dep_acc + w.maxlink + (2 * w.deplink) + (w.rightmost * l)) ∧
  0 < (w.dep_acc + w.maxlink + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.dep_acc + w.maxlink + (2 * w.deplink) + (w.clash * l)) ∧
  0 < (w.dep_acc + w.maxlink + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (w.dep_acc + w.maxlink + (2 * w.deplink) + (w.clash * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.clash * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.clash * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dep_acc + w.maxlink + (w.float * l)) ∧
  0 < (w.deplink + w.dep_acc + w.maxlink + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dep_acc + w.maxlink + (w.float * l) + (w.osd * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dep_acc + w.maxlink + w.max_acc) ∧
  0 < (w.deplink + w.dep_acc + w.maxlink + w.max_acc + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dep_acc + w.maxlink + w.max_acc + (w.osd * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.maxlink + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.maxlink) ∧
  0 < (w.deplink + w.maxlink + (w.osd * l) + (w.rightmost * l)) ∧
  0 < (w.maxlink + (w.float * l) + (w.osd * l)) ∧
  0 < (w.maxlink + w.max_acc + (w.osd * l))
def bull_pl (w : Weights) (l : ℝ) : Prop :=
  bull_pl_0 w l ∨ bull_pl_1 w l ∨ bull_pl_2 w l
def bull_sg_0 (w : Weights) (l : ℝ) : Prop :=
  0 < (((-1) * w.deplink) + ((-1) * w.dep_acc) + ((-1) * w.max_acc) + (w.float * l) + (w.osd * l)) ∧
  0 < (((-1) * w.deplink) + ((-1) * w.dep_acc) + (w.osd * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.max_acc) + (w.nonfinal * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.max_acc) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.clash * l) + (w.rightmost * l)) ∧
  0 < (((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (((-1) * w.max_acc) + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (((-1) * w.max_acc) + (w.float * l) + (w.rightmost * l)) ∧
  0 < (w.nonfinal * l) ∧
  0 < (w.rightmost * l)
def bull_sg_1 (w : Weights) (l : ℝ) : Prop :=
  0 < (((-1) * w.deplink) + ((-1) * w.dep_acc) + (w.osd * l)) ∧
  0 < (w.max_acc + ((-1) * w.deplink) + ((-1) * w.dep_acc) + (w.osd * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.dep_acc) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.dep_acc) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.max_acc + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.max_acc + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.clash * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.maxlink) + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.maxlink) + (w.clash * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.nonfinal * l) ∧
  0 < (w.rightmost * l)
def bull_sg_2 (w : Weights) (l : ℝ) : Prop :=
  0 < (w.dep_acc + w.maxlink + (2 * w.deplink) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.dep_acc + w.maxlink + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (w.dep_acc + w.maxlink + (2 * w.deplink) + (w.clash * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.clash * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dep_acc + w.maxlink + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dep_acc + w.maxlink + (w.float * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dep_acc + w.maxlink + w.max_acc + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dep_acc + w.maxlink + w.max_acc + (w.rightmost * l)) ∧
  0 < (w.deplink + w.maxlink + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.maxlink + (w.rightmost * l)) ∧
  0 < (w.maxlink + (w.float * l) + (w.osd * l)) ∧
  0 < (w.maxlink + w.max_acc + (w.osd * l))
def bull_sg (w : Weights) (l : ℝ) : Prop :=
  bull_sg_0 w l ∨ bull_sg_1 w l ∨ bull_sg_2 w l
def chief_pl_0 (w : Weights) (l : ℝ) : Prop :=
  0 < (w.osd + ((-1) * w.deplink) + ((-1) * w.dep_acc)) ∧
  0 < (w.nonfinal * l) ∧
  0 < (w.rightmost * l)
def chief_pl (w : Weights) (l : ℝ) : Prop :=
  chief_pl_0 w l
def chief_sg_0 (w : Weights) (l : ℝ) : Prop :=
  0 < (w.osd + ((-1) * w.deplink) + ((-1) * w.dep_acc)) ∧
  0 < (w.nonfinal * l)
def chief_sg (w : Weights) (l : ℝ) : Prop :=
  chief_sg_0 w l
def fut_walk_0 (w : Weights) (l : ℝ) : Prop :=
  0 < ((2 * w.max_acc) + ((-2) * w.float * l)) ∧
  0 < ((2 * w.max_acc) + (w.nonfinal * l) + ((-2) * w.float * l)) ∧
  0 < (w.max_acc + ((-1) * w.maxlink) + (w.nonfinal * l) + ((-2) * w.float * l)) ∧
  0 < (((-1) * w.deplink) + ((-1) * w.dep_acc) + (w.osd * l)) ∧
  0 < (((-1) * w.deplink) + ((-1) * w.dep_acc) + (2 * w.max_acc) + (w.osd * l) + ((-2) * w.float * l)) ∧
  0 < (w.max_acc + ((-1) * w.deplink) + ((-1) * w.dep_acc) + (w.osd * l) + ((-1) * w.float * l)) ∧
  0 < (w.max_acc + ((-1) * w.dep_acc) + (w.locality * l) + ((-2) * w.float * l)) ∧
  0 < (w.max_acc + ((-1) * w.dep_acc) + (w.locality * l) + (w.nonfinal * l) + ((-2) * w.float * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.maxlink) + (w.locality * l) + (w.nonfinal * l) + ((-2) * w.float * l)) ∧
  0 < (w.max_acc + ((-1) * w.dep_acc) + ((-2) * w.float * l)) ∧
  0 < (w.max_acc + ((-1) * w.dep_acc) + (w.nonfinal * l) + ((-2) * w.float * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.dep_acc) + (w.locality * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.dep_acc) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.dep_acc) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.max_acc + ((-1) * w.float * l)) ∧
  0 < (w.max_acc + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.maxlink) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < 0 ∧
  0 < ((2 * w.deplink) + (w.locality * l) + (w.nonfinal * l) + ((-2) * w.float * l) + (2 * w.clash * l)) ∧
  0 < (w.deplink + ((-1) * w.maxlink) + (w.locality * l) + (w.nonfinal * l) + ((-2) * w.float * l) + (2 * w.clash * l)) ∧
  0 < (w.clash + (2 * w.deplink) + (w.nonfinal * l) + ((-2) * w.float * l) + (2 * w.locality * l)) ∧
  0 < (w.clash + (2 * w.deplink) + (w.locality * l) + (w.nonfinal * l) + ((-2) * w.float * l)) ∧
  0 < (w.clash + w.deplink + w.max_acc + (w.locality * l) + ((-2) * w.float * l)) ∧
  0 < (w.clash + w.deplink + w.max_acc + (w.locality * l) + (w.nonfinal * l) + ((-2) * w.float * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.maxlink) + (w.locality * l) + (w.nonfinal * l) + ((-2) * w.float * l)) ∧
  0 < (w.clash + w.deplink + w.max_acc + ((-2) * w.float * l)) ∧
  0 < (w.clash + w.deplink + w.max_acc + (w.nonfinal * l) + ((-2) * w.float * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.maxlink) + (w.nonfinal * l) + ((-2) * w.float * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.dep_acc) + ((-2) * w.float * l) + (2 * w.locality * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.dep_acc) + (w.nonfinal * l) + ((-2) * w.float * l) + (2 * w.locality * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + (w.locality * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + (w.osd * l)) ∧
  0 < (w.clash + (2 * w.max_acc) + (w.osd * l) + ((-2) * w.float * l)) ∧
  0 < (w.clash + ((-2) * w.maxlink) + (w.nonfinal * l) + ((-2) * w.float * l)) ∧
  0 < (w.clash + w.max_acc + ((-1) * w.maxlink) + ((-2) * w.float * l)) ∧
  0 < (w.clash + w.max_acc + ((-1) * w.maxlink) + (w.nonfinal * l) + ((-2) * w.float * l)) ∧
  0 < (w.clash + ((-1) * w.deplink) + ((-1) * w.dep_acc) + ((-2) * w.maxlink) + ((-2) * w.float * l)) ∧
  0 < (w.clash + w.max_acc + ((-1) * w.deplink) + ((-1) * w.dep_acc) + ((-1) * w.maxlink) + (w.osd * l) + ((-2) * w.float * l)) ∧
  0 < (w.clash + ((-1) * w.deplink) + ((-1) * w.dep_acc) + ((-1) * w.maxlink) + (w.osd * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.max_acc + ((-1) * w.dep_acc) + (w.locality * l) + (w.osd * l) + ((-2) * w.float * l)) ∧
  0 < (w.clash + ((-1) * w.dep_acc) + ((-1) * w.maxlink) + ((-2) * w.float * l)) ∧
  0 < (w.clash + ((-1) * w.dep_acc) + ((-1) * w.maxlink) + (w.nonfinal * l) + ((-2) * w.float * l)) ∧
  0 < (w.clash + ((-1) * w.dep_acc) + (w.locality * l) + (w.osd * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.max_acc + (w.osd * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + ((-1) * w.maxlink) + ((-1) * w.float * l)) ∧
  0 < (w.clash + ((-1) * w.maxlink) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + (2 * w.deplink) + (w.clash * l) + ((-2) * w.float * l) + (2 * w.locality * l)) ∧
  0 < (w.clash + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + ((-2) * w.float * l) + (2 * w.locality * l)) ∧
  0 < (w.clash + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + ((-2) * w.float * l)) ∧
  0 < (w.clash + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + ((-2) * w.float * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.maxlink) + (w.clash * l) + (w.locality * l) + ((-2) * w.float * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.maxlink) + (w.clash * l) + ((-2) * w.float * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.maxlink) + (w.clash * l) + (w.nonfinal * l) + ((-2) * w.float * l)) ∧
  0 < (w.clash + ((-2) * w.maxlink) + (w.clash * l) + ((-2) * w.float * l)) ∧
  0 < (w.deplink + w.max_acc + (w.clash * l) + (w.locality * l) + ((-2) * w.float * l)) ∧
  0 < (w.deplink + w.max_acc + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + ((-2) * w.float * l)) ∧
  0 < (w.deplink + w.max_acc + (w.clash * l) + ((-2) * w.float * l)) ∧
  0 < (w.deplink + w.max_acc + (w.clash * l) + (w.nonfinal * l) + ((-2) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + (w.clash * l) + (w.locality * l) + ((-2) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + ((-2) * w.float * l)) ∧
  0 < (w.deplink + (w.clash * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.clash * l) + (w.locality * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.max_acc + ((-1) * w.maxlink) + (w.clash * l) + ((-2) * w.float * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.maxlink) + (w.clash * l) + (w.locality * l) + ((-2) * w.float * l)) ∧
  0 < (((-1) * w.maxlink) + (w.clash * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.max_acc + (w.locality * l) + (w.nonfinal * l) + ((-2) * w.float * l)) ∧
  0 < (w.deplink + w.max_acc + (w.nonfinal * l) + ((-2) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + (w.locality * l) + (w.nonfinal * l) + ((-2) * w.float * l)) ∧
  0 < (w.deplink + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.nonfinal * l)
def fut_walk_1 (w : Weights) (l : ℝ) : Prop :=
  0 < (((-1) * w.deplink) + ((-1) * w.max_acc) + (w.osd * l) + ((-1) * w.locality * l) + (2 * w.float * l)) ∧
  0 < (((-1) * w.deplink) + (w.float * l) + (w.osd * l) + ((-1) * w.locality * l)) ∧
  0 < (w.max_acc + ((-1) * w.deplink) + (w.osd * l) + ((-1) * w.locality * l)) ∧
  0 < ((-1) * w.locality * l) ∧
  0 < (((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.nonfinal * l)) ∧
  0 < 0 ∧
  0 < (w.dep_acc + ((-1) * w.max_acc) + (2 * w.deplink) + (w.nonfinal * l) + (2 * w.clash * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.nonfinal * l) + (2 * w.clash * l)) ∧
  0 < (w.clash + w.dep_acc + ((-1) * w.max_acc) + (2 * w.deplink) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.clash + w.dep_acc + ((-1) * w.max_acc) + (2 * w.deplink) + (w.nonfinal * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc) ∧
  0 < (w.clash + w.deplink + w.dep_acc + ((-1) * w.max_acc) + (w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + ((-1) * w.max_acc) + (w.float * l) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + ((-1) * w.max_acc) + (w.float * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + ((-1) * w.max_acc) + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + (w.nonfinal * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.nonfinal * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.max_acc) + (w.locality * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.max_acc) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.clash + w.dep_acc + ((-1) * w.max_acc) + (w.osd * l) + ((-1) * w.locality * l) + (2 * w.float * l)) ∧
  0 < (w.clash + w.dep_acc + (w.float * l) + (w.osd * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.float * l) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + w.max_acc + (w.osd * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + ((-1) * w.max_acc) + ((-2) * w.maxlink) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + ((-1) * w.maxlink) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + ((-1) * w.maxlink) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + ((-1) * w.max_acc) + (w.float * l) + (w.osd * l)) ∧
  0 < (w.clash + (w.osd * l)) ∧
  0 < (w.clash + ((-1) * w.deplink) + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.float * l) + (w.osd * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + ((-1) * w.deplink) + ((-1) * w.max_acc) + ((-2) * w.maxlink) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + ((-1) * w.deplink) + ((-1) * w.maxlink) + (w.osd * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + ((-1) * w.maxlink) + ((-1) * w.max_acc) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.clash + w.dep_acc + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l)) ∧
  0 < (w.clash + w.dep_acc + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l)) ∧
  0 < (w.clash + w.dep_acc + ((-1) * w.max_acc) + ((-2) * w.maxlink) + (w.clash * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.clash * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.max_acc) + (w.clash * l) + (w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.max_acc) + (w.clash * l) + (w.float * l) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.max_acc) + (w.clash * l) + (w.float * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.max_acc) + (w.clash * l) + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.clash * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.clash * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (w.dep_acc + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + (w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + ((-1) * w.maxlink) + (w.clash * l) + ((-1) * w.locality * l)) ∧
  0 < (((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.max_acc) + (w.float * l) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.max_acc) + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.nonfinal * l)) ∧
  0 < (w.dep_acc + ((-1) * w.max_acc) + ((-1) * w.locality * l) + (2 * w.float * l)) ∧
  0 < (w.dep_acc + ((-1) * w.max_acc) + (w.nonfinal * l) + ((-1) * w.locality * l) + (2 * w.float * l)) ∧
  0 < (w.dep_acc + (w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + (w.float * l) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.float * l) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + w.max_acc + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + w.max_acc + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + ((-1) * w.maxlink) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (((-1) * w.max_acc) + (w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (((-1) * w.max_acc) + (w.float * l) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (((-1) * w.max_acc) + (w.float * l)) ∧
  0 < (((-1) * w.max_acc) + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (w.nonfinal * l) ∧
  0 < ((w.nonfinal * l) + ((-1) * w.locality * l))
def fut_walk_2 (w : Weights) (l : ℝ) : Prop :=
  0 < (((-1) * w.deplink) + (w.float * l) + (w.osd * l) + ((-1) * w.locality * l)) ∧
  0 < (((-1) * w.deplink) + (2 * w.max_acc) + (w.osd * l) + ((-1) * w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.max_acc + ((-1) * w.deplink) + (w.osd * l) + ((-1) * w.locality * l)) ∧
  0 < (w.max_acc + ((-1) * w.float * l)) ∧
  0 < (w.max_acc + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.max_acc + ((-1) * w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.max_acc + (w.nonfinal * l) + ((-1) * w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (((-1) * w.maxlink) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < ((-1) * w.locality * l) ∧
  0 < 0 ∧
  0 < (w.dep_acc + (2 * w.deplink) + (w.nonfinal * l) + ((-1) * w.float * l) + (2 * w.clash * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.maxlink) + (w.nonfinal * l) + ((-1) * w.float * l) + (2 * w.clash * l)) ∧
  0 < (w.clash + w.dep_acc + (2 * w.deplink) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.dep_acc + (2 * w.deplink) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc) ∧
  0 < (w.clash + w.deplink + w.dep_acc + (w.nonfinal * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + w.max_acc + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + w.max_acc + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + w.max_acc + ((-1) * w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + w.max_acc + (w.nonfinal * l) + ((-1) * w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + ((-1) * w.maxlink) + (w.nonfinal * l) + ((-1) * w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + ((-1) * w.maxlink) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.deplink + (w.locality * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.dep_acc + (w.float * l) + (w.osd * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + (2 * w.max_acc) + (w.osd * l) + ((-1) * w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + ((-2) * w.maxlink) + (w.nonfinal * l) + ((-1) * w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + w.max_acc + ((-1) * w.maxlink) + ((-1) * w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + w.max_acc + ((-1) * w.maxlink) + (w.nonfinal * l) + ((-1) * w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + w.max_acc + (w.osd * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + ((-1) * w.maxlink) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + ((-1) * w.maxlink) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + (w.osd * l)) ∧
  0 < (w.clash + ((-1) * w.deplink) + ((-2) * w.maxlink) + ((-1) * w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.max_acc + ((-1) * w.deplink) + ((-1) * w.maxlink) + (w.osd * l) + ((-1) * w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + ((-1) * w.deplink) + ((-1) * w.maxlink) + (w.osd * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.max_acc + (w.osd * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + ((-1) * w.maxlink) + ((-1) * w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + ((-1) * w.maxlink) + (w.nonfinal * l) + ((-1) * w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + (2 * w.deplink) + (w.clash * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.dep_acc + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.dep_acc + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.dep_acc + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + ((-1) * w.maxlink) + (w.clash * l) + ((-1) * w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + ((-1) * w.maxlink) + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + ((-1) * w.maxlink) + (w.clash * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.dep_acc + ((-2) * w.maxlink) + (w.clash * l) + ((-1) * w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.clash * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dep_acc + w.max_acc + (w.clash * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.dep_acc + w.max_acc + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.dep_acc + w.max_acc + (w.clash * l) + ((-1) * w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + w.max_acc + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.clash * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + (w.clash * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.dep_acc + w.max_acc + ((-1) * w.maxlink) + (w.clash * l) + ((-1) * w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + ((-1) * w.maxlink) + (w.clash * l) + ((-1) * w.locality * l)) ∧
  0 < (((-1) * w.maxlink) + (w.clash * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dep_acc + w.max_acc + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.dep_acc + w.max_acc + (w.nonfinal * l) + ((-1) * w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.dep_acc + (w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + (w.float * l) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + (2 * w.max_acc) + ((-1) * w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + (2 * w.max_acc) + (w.nonfinal * l) + ((-1) * w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + w.max_acc + ((-1) * w.maxlink) + (w.nonfinal * l) + ((-1) * w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + w.max_acc + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + w.max_acc + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + ((-1) * w.maxlink) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.nonfinal * l) ∧
  0 < ((w.nonfinal * l) + ((-1) * w.locality * l))
def fut_walk_3 (w : Weights) (l : ℝ) : Prop :=
  0 < (((-1) * w.deplink) + ((-1) * w.dep_acc) + ((-2) * w.max_acc) + (w.osd * l) + (2 * w.float * l)) ∧
  0 < (((-1) * w.deplink) + ((-1) * w.dep_acc) + ((-1) * w.max_acc) + (w.float * l) + (w.osd * l)) ∧
  0 < (((-1) * w.deplink) + ((-1) * w.dep_acc) + (w.osd * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-2) * w.max_acc) + (w.float * l) + (w.locality * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-2) * w.max_acc) + (w.float * l) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-2) * w.max_acc) + (w.float * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-2) * w.max_acc) + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.maxlink) + ((-2) * w.max_acc) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.max_acc) + (w.locality * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.max_acc) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.max_acc)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.max_acc) + (w.nonfinal * l)) ∧
  0 < (((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.nonfinal * l)) ∧
  0 < 0 ∧
  0 < (((-2) * w.max_acc) + (2 * w.deplink) + (w.locality * l) + (w.nonfinal * l) + (2 * w.clash * l)) ∧
  0 < (w.deplink + ((-1) * w.maxlink) + ((-2) * w.max_acc) + (w.locality * l) + (w.nonfinal * l) + (2 * w.clash * l)) ∧
  0 < (((-2) * w.max_acc) + (2 * w.float * l)) ∧
  0 < (((-2) * w.max_acc) + (w.nonfinal * l) + (2 * w.float * l)) ∧
  0 < (w.clash + ((-2) * w.max_acc) + (2 * w.deplink) + (w.nonfinal * l) + (2 * w.locality * l)) ∧
  0 < (w.clash + ((-2) * w.max_acc) + (2 * w.deplink) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.clash + ((-2) * w.max_acc) + (w.osd * l) + (2 * w.float * l)) ∧
  0 < (w.clash + w.deplink + ((-2) * w.max_acc) + (w.float * l) + (w.locality * l)) ∧
  0 < (w.clash + w.deplink + ((-2) * w.max_acc) + (w.float * l) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.clash + w.deplink + ((-2) * w.max_acc) + (w.float * l)) ∧
  0 < (w.clash + w.deplink + ((-2) * w.max_acc) + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.maxlink) + ((-2) * w.max_acc) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.max_acc) + (w.locality * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.max_acc) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.dep_acc) + ((-2) * w.max_acc) + (2 * w.locality * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.dep_acc) + ((-2) * w.max_acc) + (w.nonfinal * l) + (2 * w.locality * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.maxlink) + ((-2) * w.max_acc) + (w.nonfinal * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.max_acc)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.max_acc) + (w.nonfinal * l)) ∧
  0 < (w.clash + ((-1) * w.maxlink) + ((-2) * w.max_acc) + (w.float * l)) ∧
  0 < (w.clash + ((-1) * w.maxlink) + ((-2) * w.max_acc) + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (w.clash + ((-1) * w.max_acc) + (w.float * l) + (w.osd * l)) ∧
  0 < (w.clash + (w.osd * l)) ∧
  0 < (w.clash + ((-2) * w.maxlink) + ((-2) * w.max_acc) + (w.nonfinal * l)) ∧
  0 < (w.clash + ((-1) * w.deplink) + ((-1) * w.dep_acc) + ((-1) * w.maxlink) + ((-2) * w.max_acc) + (w.float * l) + (w.osd * l)) ∧
  0 < (w.clash + ((-1) * w.deplink) + ((-1) * w.dep_acc) + ((-2) * w.maxlink) + ((-2) * w.max_acc)) ∧
  0 < (w.clash + ((-1) * w.deplink) + ((-1) * w.dep_acc) + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.osd * l)) ∧
  0 < (w.clash + ((-1) * w.dep_acc) + ((-2) * w.max_acc) + (w.float * l) + (w.locality * l) + (w.osd * l)) ∧
  0 < (w.clash + ((-1) * w.dep_acc) + ((-1) * w.max_acc) + (w.locality * l) + (w.osd * l)) ∧
  0 < (w.clash + ((-1) * w.dep_acc) + ((-1) * w.maxlink) + ((-2) * w.max_acc)) ∧
  0 < (w.clash + ((-1) * w.dep_acc) + ((-1) * w.maxlink) + ((-2) * w.max_acc) + (w.nonfinal * l)) ∧
  0 < (w.clash + ((-1) * w.maxlink) + ((-1) * w.max_acc)) ∧
  0 < (w.clash + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.nonfinal * l)) ∧
  0 < (w.clash + ((-2) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (2 * w.locality * l)) ∧
  0 < (w.clash + ((-2) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (2 * w.locality * l)) ∧
  0 < (w.clash + ((-2) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.locality * l)) ∧
  0 < (w.clash + ((-2) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.maxlink) + ((-2) * w.max_acc) + (w.clash * l) + (w.locality * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.maxlink) + ((-2) * w.max_acc) + (w.clash * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.maxlink) + ((-2) * w.max_acc) + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (w.clash + ((-2) * w.maxlink) + ((-2) * w.max_acc) + (w.clash * l)) ∧
  0 < (w.deplink + ((-2) * w.max_acc) + (w.clash * l) + (w.float * l) + (w.locality * l)) ∧
  0 < (w.deplink + ((-2) * w.max_acc) + (w.clash * l) + (w.float * l) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-2) * w.max_acc) + (w.clash * l) + (w.float * l)) ∧
  0 < (w.deplink + ((-2) * w.max_acc) + (w.clash * l) + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.clash * l) + (w.locality * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + ((-2) * w.max_acc) + (w.clash * l) + (w.locality * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + ((-2) * w.max_acc) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.clash * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (((-1) * w.maxlink) + ((-2) * w.max_acc) + (w.clash * l) + (w.float * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.maxlink) + ((-2) * w.max_acc) + (w.clash * l) + (w.locality * l)) ∧
  0 < (((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l)) ∧
  0 < (w.deplink + ((-2) * w.max_acc) + (w.float * l) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-2) * w.max_acc) + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + ((-2) * w.max_acc) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.nonfinal * l)) ∧
  0 < (((-1) * w.maxlink) + ((-2) * w.max_acc) + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (((-1) * w.max_acc) + (w.float * l)) ∧
  0 < (((-1) * w.max_acc) + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (w.nonfinal * l)
def fut_walk_4 (w : Weights) (l : ℝ) : Prop :=
  0 < (((-1) * w.deplink) + ((-1) * w.dep_acc) + ((-1) * w.max_acc) + (w.float * l) + (w.osd * l)) ∧
  0 < (((-1) * w.deplink) + ((-1) * w.dep_acc) + (w.osd * l)) ∧
  0 < (w.max_acc + ((-1) * w.deplink) + ((-1) * w.dep_acc) + (w.osd * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.max_acc) + (w.locality * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.max_acc) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.dep_acc) + (w.locality * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.dep_acc) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.dep_acc) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.max_acc)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.max_acc) + (w.nonfinal * l)) ∧
  0 < (w.max_acc + ((-1) * w.float * l)) ∧
  0 < (w.max_acc + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.maxlink) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.nonfinal * l)) ∧
  0 < 0 ∧
  0 < (((-1) * w.max_acc) + (2 * w.deplink) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l) + (2 * w.clash * l)) ∧
  0 < (w.deplink + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l) + (2 * w.clash * l)) ∧
  0 < (w.clash + ((-1) * w.max_acc) + (2 * w.deplink) + (w.nonfinal * l) + ((-1) * w.float * l) + (2 * w.locality * l)) ∧
  0 < (w.clash + ((-1) * w.max_acc) + (2 * w.deplink) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.max_acc) + (w.locality * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.max_acc) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.dep_acc) + ((-1) * w.max_acc) + ((-1) * w.float * l) + (2 * w.locality * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.dep_acc) + ((-1) * w.max_acc) + (w.nonfinal * l) + ((-1) * w.float * l) + (2 * w.locality * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + (w.locality * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.max_acc)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.max_acc) + (w.nonfinal * l)) ∧
  0 < (w.clash + ((-1) * w.max_acc) + (w.float * l) + (w.osd * l)) ∧
  0 < (w.clash + (w.osd * l)) ∧
  0 < (w.clash + ((-1) * w.deplink) + ((-1) * w.dep_acc) + ((-1) * w.max_acc) + ((-2) * w.maxlink) + ((-1) * w.float * l)) ∧
  0 < (w.clash + ((-1) * w.deplink) + ((-1) * w.dep_acc) + ((-1) * w.maxlink) + (w.osd * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + ((-1) * w.deplink) + ((-1) * w.dep_acc) + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.osd * l)) ∧
  0 < (w.clash + ((-1) * w.dep_acc) + ((-1) * w.max_acc) + (w.locality * l) + (w.osd * l)) ∧
  0 < (w.clash + ((-1) * w.dep_acc) + (w.locality * l) + (w.osd * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + ((-1) * w.dep_acc) + ((-1) * w.maxlink) + ((-1) * w.max_acc) + ((-1) * w.float * l)) ∧
  0 < (w.clash + ((-1) * w.dep_acc) + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.max_acc + (w.osd * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + ((-1) * w.max_acc) + ((-2) * w.maxlink) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + ((-1) * w.maxlink) + ((-1) * w.float * l)) ∧
  0 < (w.clash + ((-1) * w.maxlink) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + ((-1) * w.maxlink) + ((-1) * w.max_acc)) ∧
  0 < (w.clash + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.nonfinal * l)) ∧
  0 < (w.clash + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + ((-1) * w.float * l) + (2 * w.locality * l)) ∧
  0 < (w.clash + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.float * l) + (2 * w.locality * l)) ∧
  0 < (w.clash + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + (w.locality * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + ((-1) * w.max_acc) + ((-2) * w.maxlink) + (w.clash * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.clash * l) + (w.locality * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + ((-1) * w.max_acc) + (w.clash * l) + (w.locality * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + ((-1) * w.max_acc) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.clash * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.clash * l) + (w.locality * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.clash * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + (w.locality * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.maxlink) + (w.clash * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + ((-1) * w.max_acc) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.nonfinal * l)) ∧
  0 < (((-1) * w.max_acc) + (w.float * l)) ∧
  0 < (((-1) * w.max_acc) + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (w.nonfinal * l)
def fut_walk_5 (w : Weights) (l : ℝ) : Prop :=
  0 < (w.maxlink + (2 * w.max_acc) + (w.osd * l) + ((-1) * w.float * l)) ∧
  0 < (w.dep_acc + (2 * w.deplink) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l) + (2 * w.clash * l)) ∧
  0 < (w.dep_acc + w.maxlink + (3 * w.deplink) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l) + (2 * w.clash * l)) ∧
  0 < (w.dep_acc + w.maxlink + (2 * w.deplink) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.dep_acc + w.maxlink + (2 * w.deplink) + (w.nonfinal * l)) ∧
  0 < (w.dep_acc + w.maxlink + w.max_acc + (2 * w.deplink) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.dep_acc + w.maxlink + w.max_acc + (2 * w.deplink) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.maxlink + (2 * w.deplink) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + (2 * w.deplink) + (w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + (2 * w.deplink) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + (2 * w.deplink)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + (2 * w.deplink) + (w.nonfinal * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + w.max_acc + (2 * w.deplink) + (w.locality * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + w.max_acc + (2 * w.deplink) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.dep_acc + (2 * w.deplink) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + w.max_acc + (2 * w.deplink) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + w.max_acc + (2 * w.deplink) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.dep_acc + (2 * w.deplink) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.maxlink + (2 * w.deplink) + ((-1) * w.float * l) + (2 * w.locality * l)) ∧
  0 < (w.clash + w.maxlink + (2 * w.deplink) + (w.nonfinal * l) + ((-1) * w.float * l) + (2 * w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + (3 * w.deplink) + (w.nonfinal * l) + ((-1) * w.float * l) + (2 * w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + (3 * w.deplink) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc) ∧
  0 < (w.clash + w.deplink + w.dep_acc + w.maxlink + (w.float * l) + (w.osd * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + w.maxlink + w.max_acc + (w.osd * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + (w.nonfinal * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + w.maxlink + (2 * w.max_acc) + (w.osd * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + w.max_acc + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + w.max_acc + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + ((-1) * w.maxlink) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + w.maxlink + (w.locality * l) + (w.osd * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + w.maxlink + w.max_acc + (w.locality * l) + (w.osd * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + (w.osd * l)) ∧
  0 < (w.clash + w.max_acc + (w.osd * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + ((-1) * w.maxlink) + ((-1) * w.float * l)) ∧
  0 < (w.dep_acc + w.maxlink + (2 * w.deplink) + (w.clash * l) + (w.locality * l)) ∧
  0 < (w.dep_acc + w.maxlink + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.dep_acc + w.maxlink + (2 * w.deplink) + (w.clash * l)) ∧
  0 < (w.dep_acc + w.maxlink + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (w.dep_acc + w.maxlink + w.max_acc + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + ((-1) * w.float * l)) ∧
  0 < (w.dep_acc + w.maxlink + w.max_acc + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.dep_acc + w.maxlink + w.max_acc + (2 * w.deplink) + (w.clash * l) + ((-1) * w.float * l)) ∧
  0 < (w.dep_acc + w.maxlink + w.max_acc + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.maxlink + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + ((-1) * w.float * l)) ∧
  0 < (w.maxlink + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.dep_acc + (2 * w.deplink) + (w.clash * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.dep_acc + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.dep_acc + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + (3 * w.deplink) + (w.clash * l) + ((-1) * w.float * l) + (2 * w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + (3 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.float * l) + (2 * w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + (3 * w.deplink) + (w.clash * l) + (w.locality * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + (3 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + ((-1) * w.maxlink) + (w.clash * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.clash * l)) ∧
  0 < (w.deplink + w.dep_acc + w.max_acc + (w.clash * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.clash * l) + (w.locality * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.dep_acc + w.maxlink + (w.float * l)) ∧
  0 < (w.deplink + w.dep_acc + w.maxlink + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dep_acc + w.maxlink + w.max_acc) ∧
  0 < (w.deplink + w.dep_acc + w.maxlink + w.max_acc + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dep_acc + w.maxlink + (2 * w.max_acc) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.dep_acc + w.maxlink + (2 * w.max_acc) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.dep_acc + w.max_acc + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.maxlink + (w.locality * l)) ∧
  0 < (w.deplink + w.maxlink + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.maxlink) ∧
  0 < (w.deplink + w.maxlink + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.maxlink + w.max_acc + (w.locality * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.maxlink + w.max_acc + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.maxlink + w.max_acc + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.maxlink + w.max_acc + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.maxlink + (w.float * l) + (w.osd * l)) ∧
  0 < (w.maxlink + w.max_acc + (w.osd * l))
def fut_walk_6 (w : Weights) (l : ℝ) : Prop :=
  0 < (w.dep_acc + ((-1) * w.max_acc) + (2 * w.deplink) + (w.locality * l) + (w.nonfinal * l) + (2 * w.clash * l)) ∧
  0 < (w.dep_acc + w.maxlink + ((-1) * w.max_acc) + (3 * w.deplink) + (w.locality * l) + (w.nonfinal * l) + (2 * w.clash * l)) ∧
  0 < (w.dep_acc + w.maxlink + ((-1) * w.max_acc) + (2 * w.deplink) + (w.float * l) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.dep_acc + w.maxlink + ((-1) * w.max_acc) + (2 * w.deplink) + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (w.dep_acc + w.maxlink + (2 * w.deplink) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.dep_acc + w.maxlink + (2 * w.deplink) + (w.nonfinal * l)) ∧
  0 < (w.maxlink + ((-1) * w.max_acc) + (2 * w.deplink) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.maxlink + ((-1) * w.max_acc) + (w.osd * l) + (2 * w.float * l)) ∧
  0 < (w.clash + w.maxlink + ((-1) * w.max_acc) + (2 * w.deplink) + (2 * w.locality * l)) ∧
  0 < (w.clash + w.maxlink + ((-1) * w.max_acc) + (2 * w.deplink) + (w.nonfinal * l) + (2 * w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + ((-1) * w.max_acc) + (2 * w.deplink) + (w.float * l) + (w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + ((-1) * w.max_acc) + (2 * w.deplink) + (w.float * l) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + ((-1) * w.max_acc) + (2 * w.deplink) + (w.float * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + ((-1) * w.max_acc) + (2 * w.deplink) + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + (2 * w.deplink) + (w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + (2 * w.deplink) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.clash + w.dep_acc + ((-1) * w.max_acc) + (2 * w.deplink) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + (2 * w.deplink)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + (2 * w.deplink) + (w.nonfinal * l)) ∧
  0 < (w.clash + w.dep_acc + ((-1) * w.max_acc) + (2 * w.deplink) + (w.nonfinal * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + ((-1) * w.max_acc) + (3 * w.deplink) + (w.nonfinal * l) + (2 * w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + ((-1) * w.max_acc) + (3 * w.deplink) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc) ∧
  0 < (w.clash + w.deplink + w.dep_acc + w.maxlink + ((-1) * w.max_acc) + (w.osd * l) + (2 * w.float * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + w.maxlink + (w.float * l) + (w.osd * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + ((-1) * w.max_acc) + (w.float * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + ((-1) * w.max_acc) + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + w.maxlink + w.max_acc + (w.osd * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + (w.nonfinal * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.nonfinal * l)) ∧
  0 < (w.clash + w.deplink + w.maxlink + ((-1) * w.max_acc) + (w.float * l) + (w.locality * l) + (w.osd * l)) ∧
  0 < (w.clash + w.deplink + w.maxlink + (w.locality * l) + (w.osd * l)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.max_acc)) ∧
  0 < (w.clash + w.deplink + ((-1) * w.max_acc) + (w.nonfinal * l)) ∧
  0 < (w.clash + ((-1) * w.max_acc) + (w.float * l) + (w.osd * l)) ∧
  0 < (w.clash + (w.osd * l)) ∧
  0 < (w.clash + ((-1) * w.maxlink) + ((-1) * w.max_acc)) ∧
  0 < (w.dep_acc + w.maxlink + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.float * l) + (w.locality * l)) ∧
  0 < (w.dep_acc + w.maxlink + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.float * l) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.dep_acc + w.maxlink + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.float * l)) ∧
  0 < (w.dep_acc + w.maxlink + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (w.dep_acc + w.maxlink + (2 * w.deplink) + (w.clash * l) + (w.locality * l)) ∧
  0 < (w.dep_acc + w.maxlink + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.dep_acc + w.maxlink + (2 * w.deplink) + (w.clash * l)) ∧
  0 < (w.dep_acc + w.maxlink + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (w.maxlink + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.locality * l)) ∧
  0 < (w.maxlink + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.clash + w.dep_acc + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l)) ∧
  0 < (w.clash + w.dep_acc + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + ((-1) * w.max_acc) + (3 * w.deplink) + (w.clash * l) + (2 * w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + ((-1) * w.max_acc) + (3 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (2 * w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + ((-1) * w.max_acc) + (3 * w.deplink) + (w.clash * l) + (w.locality * l)) ∧
  0 < (w.clash + w.dep_acc + w.maxlink + ((-1) * w.max_acc) + (3 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.clash + w.deplink + w.dep_acc + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.clash * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.max_acc) + (w.clash * l) + (w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.clash * l) + (w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + w.maxlink + ((-1) * w.max_acc) + (2 * w.float * l)) ∧
  0 < (w.deplink + w.dep_acc + w.maxlink + ((-1) * w.max_acc) + (w.nonfinal * l) + (2 * w.float * l)) ∧
  0 < (w.deplink + w.dep_acc + w.maxlink + (w.float * l)) ∧
  0 < (w.deplink + w.dep_acc + w.maxlink + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.max_acc) + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dep_acc + w.maxlink + w.max_acc) ∧
  0 < (w.deplink + w.dep_acc + w.maxlink + w.max_acc + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.maxlink + ((-1) * w.max_acc) + (w.float * l) + (w.locality * l)) ∧
  0 < (w.deplink + w.maxlink + ((-1) * w.max_acc) + (w.float * l) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.maxlink + ((-1) * w.max_acc) + (w.float * l)) ∧
  0 < (w.deplink + w.maxlink + ((-1) * w.max_acc) + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.maxlink + (w.locality * l)) ∧
  0 < (w.deplink + w.maxlink + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.maxlink) ∧
  0 < (w.deplink + w.maxlink + (w.nonfinal * l)) ∧
  0 < (w.maxlink + (w.float * l) + (w.osd * l)) ∧
  0 < (w.maxlink + w.max_acc + (w.osd * l))
def fut_walk (w : Weights) (l : ℝ) : Prop :=
  fut_walk_0 w l ∨ fut_walk_1 w l ∨ fut_walk_2 w l ∨ fut_walk_3 w l ∨ fut_walk_4 w l ∨ fut_walk_5 w l ∨ fut_walk_6 w l
def owl_2_0 (w : Weights) (l : ℝ) : Prop :=
  0 < (((-1) * w.deplink) + ((-1) * w.dep_acc) + ((-1) * w.max_acc) + (w.float * l) + (w.osd * l)) ∧
  0 < (((-1) * w.deplink) + ((-1) * w.dep_acc) + (w.osd * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.max_acc) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.max_acc) + (w.locality * l) + (w.osd * l) + (w.rightmost * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.max_acc)) ∧
  0 < (((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.nonfinal * l)) ∧
  0 < 0 ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.clash * l) + (w.locality * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.clash * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l)) ∧
  0 < (((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.locality * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.rightmost * l)) ∧
  0 < (((-1) * w.max_acc) + (w.float * l)) ∧
  0 < (((-1) * w.max_acc) + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (((-1) * w.max_acc) + (w.float * l) + (w.osd * l) + (w.rightmost * l)) ∧
  0 < (w.nonfinal * l) ∧
  0 < ((w.osd * l) + (w.rightmost * l))
def owl_2_1 (w : Weights) (l : ℝ) : Prop :=
  0 < (((-1) * w.deplink) + ((-1) * w.dep_acc) + (w.osd * l)) ∧
  0 < (w.max_acc + ((-1) * w.deplink) + ((-1) * w.dep_acc) + (w.osd * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.dep_acc) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.dep_acc) + (w.locality * l) + (w.osd * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.max_acc + ((-1) * w.float * l)) ∧
  0 < (w.max_acc + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.max_acc + (w.osd * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.maxlink) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < 0 ∧
  0 < (w.deplink + (w.clash * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.clash * l) + (w.locality * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.maxlink) + (w.clash * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.maxlink) + (w.clash * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.locality * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.nonfinal * l) ∧
  0 < ((w.osd * l) + (w.rightmost * l))
def owl_2_2 (w : Weights) (l : ℝ) : Prop :=
  0 < (w.dep_acc + w.maxlink + (2 * w.deplink) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.dep_acc + w.maxlink + (2 * w.deplink) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.dep_acc + w.maxlink + (2 * w.deplink) + (w.locality * l) + (w.rightmost * l)) ∧
  0 < (w.dep_acc + w.maxlink + (2 * w.deplink) + (w.rightmost * l)) ∧
  0 < (w.dep_acc + w.maxlink + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.dep_acc + w.maxlink + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.rightmost * l)) ∧
  0 < (w.dep_acc + w.maxlink + (2 * w.deplink) + (w.clash * l)) ∧
  0 < (w.dep_acc + w.maxlink + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.clash * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.clash * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dep_acc + w.maxlink + (w.float * l)) ∧
  0 < (w.deplink + w.dep_acc + w.maxlink + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dep_acc + w.maxlink + (w.float * l) + (w.osd * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dep_acc + w.maxlink + w.max_acc) ∧
  0 < (w.deplink + w.dep_acc + w.maxlink + w.max_acc + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dep_acc + w.maxlink + w.max_acc + (w.osd * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.maxlink + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.maxlink + (w.locality * l) + (w.osd * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.maxlink) ∧
  0 < (w.maxlink + (w.float * l) + (w.osd * l)) ∧
  0 < (w.maxlink + w.max_acc + (w.osd * l))
def owl_2 (w : Weights) (l : ℝ) : Prop :=
  owl_2_0 w l ∨ owl_2_1 w l ∨ owl_2_2 w l
def owl_3_0 (w : Weights) (l : ℝ) : Prop :=
  0 < (w.osd + ((-1) * w.dep_acc) + ((-2) * w.deplink) + (w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.max_acc + w.osd + ((-1) * w.dep_acc) + ((-2) * w.deplink) + ((-1) * w.locality * l)) ∧
  0 < (w.osd + ((-1) * w.dep_acc) + ((-1) * w.maxlink) + ((-2) * w.deplink) + ((-1) * w.locality * l)) ∧
  0 < (((-1) * w.deplink) + (w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (((-1) * w.deplink) + (w.float * l) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.osd + ((-1) * w.deplink) + (w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.osd + ((-1) * w.deplink) + (w.float * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (((-1) * w.deplink) + (w.float * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (((-1) * w.deplink) + ((-1) * w.dep_acc)) ∧
  0 < (((-1) * w.deplink) + ((-1) * w.dep_acc) + (w.nonfinal * l)) ∧
  0 < (w.osd + ((-1) * w.deplink) + ((-1) * w.dep_acc) + (w.rightmost * l)) ∧
  0 < (((-1) * w.deplink) + ((-1) * w.dep_acc) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.max_acc + ((-1) * w.deplink) + ((-1) * w.locality * l)) ∧
  0 < (w.max_acc + ((-1) * w.deplink) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.max_acc + w.osd + ((-1) * w.deplink) + ((-1) * w.locality * l)) ∧
  0 < (w.max_acc + w.osd + ((-1) * w.deplink) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.max_acc + ((-1) * w.deplink) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (((-1) * w.deplink) + ((-1) * w.maxlink) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (2 * w.rightmost * l) ∧
  0 < (w.osd + (w.clash * l) + (w.rightmost * l)) ∧
  0 < (w.osd + ((-1) * w.deplink) + ((-1) * w.maxlink) + (w.clash * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (((-1) * w.deplink) + ((-1) * w.maxlink) + (w.clash * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.nonfinal * l) ∧
  0 < (w.rightmost * l) ∧
  0 < (((-1) * w.locality * l) + (2 * w.rightmost * l)) ∧
  0 < ((w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < ((w.clash * l) + (w.nonfinal * l)) ∧
  0 < ((w.clash * l) + (w.rightmost * l)) ∧
  0 < ((w.clash * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < ((w.nonfinal * l) + (w.rightmost * l))
def owl_3_1 (w : Weights) (l : ℝ) : Prop :=
  0 < (w.maxlink + w.osd + ((-1) * w.deplink) + ((-1) * w.dep_acc) + (w.float * l)) ∧
  0 < (w.maxlink + w.max_acc + w.osd + ((-1) * w.deplink) + ((-1) * w.dep_acc)) ∧
  0 < (w.osd + ((-1) * w.deplink) + ((-1) * w.dep_acc)) ∧
  0 < (w.maxlink + ((-1) * w.dep_acc) + (w.locality * l)) ∧
  0 < (w.maxlink + ((-1) * w.dep_acc) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.maxlink + w.osd + ((-1) * w.dep_acc) + (w.locality * l) + (w.rightmost * l)) ∧
  0 < (w.maxlink + ((-1) * w.dep_acc) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.maxlink + (w.clash * l) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.maxlink + w.osd + (w.clash * l) + (w.locality * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.maxlink + (w.clash * l) + (w.locality * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.maxlink + (w.clash * l) + (w.rightmost * l)) ∧
  0 < (w.osd + (w.clash * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.maxlink + (w.locality * l) + (2 * w.rightmost * l)) ∧
  0 < (w.deplink + w.maxlink + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.maxlink + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.maxlink + (w.locality * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.maxlink + (2 * w.rightmost * l)) ∧
  0 < (w.deplink + w.maxlink + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.maxlink + (w.float * l)) ∧
  0 < (w.maxlink + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (w.maxlink + w.osd + (w.float * l)) ∧
  0 < (w.maxlink + w.osd + (w.float * l) + (w.rightmost * l)) ∧
  0 < (w.maxlink + (w.float * l) + (w.rightmost * l)) ∧
  0 < (w.maxlink + w.max_acc) ∧
  0 < (w.maxlink + w.max_acc + (w.nonfinal * l)) ∧
  0 < (w.maxlink + w.max_acc + w.osd) ∧
  0 < (w.maxlink + w.max_acc + w.osd + (w.rightmost * l)) ∧
  0 < (w.maxlink + w.max_acc + (w.rightmost * l)) ∧
  0 < (w.nonfinal * l) ∧
  0 < ((w.clash * l) + (w.rightmost * l))
def owl_3 (w : Weights) (l : ℝ) : Prop :=
  owl_3_0 w l ∨ owl_3_1 w l
def owl_sg_0 (w : Weights) (l : ℝ) : Prop :=
  0 < (((-1) * w.deplink) + ((-1) * w.dep_acc) + ((-1) * w.max_acc) + (w.float * l) + (w.osd * l)) ∧
  0 < (((-1) * w.deplink) + ((-1) * w.dep_acc) + (w.osd * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.max_acc) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (((-1) * w.max_acc) + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (w.nonfinal * l)
def owl_sg_1 (w : Weights) (l : ℝ) : Prop :=
  0 < (((-1) * w.deplink) + ((-1) * w.dep_acc) + (w.osd * l)) ∧
  0 < (w.max_acc + ((-1) * w.deplink) + ((-1) * w.dep_acc) + (w.osd * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.dep_acc) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.max_acc + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.maxlink) + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.nonfinal * l)
def owl_sg_2 (w : Weights) (l : ℝ) : Prop :=
  0 < (w.dep_acc + w.maxlink + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dep_acc + w.maxlink + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dep_acc + w.maxlink + w.max_acc + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.maxlink + (w.nonfinal * l)) ∧
  0 < (w.maxlink + (w.float * l) + (w.osd * l)) ∧
  0 < (w.maxlink + w.max_acc + (w.osd * l))
def owl_sg (w : Weights) (l : ℝ) : Prop :=
  owl_sg_0 w l ∨ owl_sg_1 w l ∨ owl_sg_2 w l
def spring_loc_0 (w : Weights) (l : ℝ) : Prop :=
  0 < (w.dock_prev + w.float + w.max_acc + ((-1) * w.deplink) + (w.osd * l)) ∧
  0 < (w.dock_prev + w.float + ((-1) * w.deplink) + (w.osd * l)) ∧
  0 < (w.dock_prev + w.float + ((-1) * w.deplink) + ((-1) * w.maxlink)) ∧
  0 < (w.dock_prev + w.float + ((-1) * w.deplink) + ((-1) * w.maxlink) + ((-1) * w.max_acc)) ∧
  0 < (w.dock_prev + w.float + ((-1) * w.deplink) + (w.float * l) + (w.osd * l)) ∧
  0 < (w.dock_prev + w.float + ((-1) * w.deplink) + ((-1) * w.max_acc) + (w.float * l) + (w.osd * l)) ∧
  0 < (w.dep_acc + w.dock_prev + ((-1) * w.max_acc) + (2 * w.deplink) + (w.locality * l) + (w.nonfinal * l) + (2 * w.clash * l)) ∧
  0 < (w.dep_acc + w.dock_prev + ((-1) * w.max_acc) + (2 * w.deplink) + (w.locality * l) + (w.rightmost * l) + (2 * w.clash * l)) ∧
  0 < (w.dep_acc + w.dock_prev + ((-1) * w.max_acc) + (2 * w.deplink) + (w.rightmost * l) + (2 * w.clash * l)) ∧
  0 < (w.dep_acc + ((-1) * w.max_acc) + (2 * w.deplink) + (w.locality * l) + (w.nonfinal * l) + (2 * w.clash * l)) ∧
  0 < (w.dep_acc + ((-1) * w.max_acc) + (2 * w.deplink) + (w.rightmost * l) + (2 * w.clash * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.nonfinal * l) + (2 * w.clash * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.rightmost * l) + (2 * w.clash * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.nonfinal * l) + (2 * w.clash * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.rightmost * l) + (2 * w.clash * l)) ∧
  0 < (w.dep_acc + w.dock_prev + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.dep_acc + w.dock_prev + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.dep_acc + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.dep_acc + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.clash * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + (w.clash * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + w.float + (w.clash * l) + (w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + w.float + (w.clash * l) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + w.float + ((-1) * w.max_acc) + (w.clash * l) + (w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + w.float + ((-1) * w.max_acc) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + w.float + (w.clash * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + w.float + ((-1) * w.max_acc) + (w.clash * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + ((-1) * w.max_acc) + (w.clash * l) + (w.float * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + ((-1) * w.max_acc) + (w.clash * l) + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + ((-1) * w.max_acc) + (w.clash * l) + (w.float * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + (w.clash * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.max_acc) + (w.clash * l) + (w.float * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.max_acc) + (w.clash * l) + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dock_prev + ((-1) * w.max_acc) + (w.clash * l) + (w.locality * l)) ∧
  0 < (w.deplink + w.dock_prev + ((-1) * w.max_acc) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dock_prev + ((-1) * w.max_acc) + (w.clash * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.dep_acc + w.dock_prev + w.float + ((-1) * w.maxlink) + (w.clash * l)) ∧
  0 < (w.dep_acc + w.dock_prev + w.float + ((-1) * w.maxlink) + (w.clash * l) + (w.rightmost * l)) ∧
  0 < (w.dep_acc + w.dock_prev + w.float + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l)) ∧
  0 < (w.dep_acc + w.dock_prev + w.float + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + (w.rightmost * l)) ∧
  0 < (w.dock_prev + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + (w.rightmost * l)) ∧
  0 < (((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + w.float + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + w.float + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + w.float + (w.locality * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + w.float + ((-1) * w.max_acc) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + w.float + ((-1) * w.max_acc) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + w.float + ((-1) * w.max_acc) + (w.locality * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + w.float + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + w.float + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + w.float + ((-1) * w.max_acc) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + w.float + ((-1) * w.max_acc) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + ((-1) * w.max_acc) + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + ((-1) * w.max_acc) + (w.float * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + ((-1) * w.max_acc) + (w.float * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.max_acc) + (w.float * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dock_prev + ((-1) * w.max_acc) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dock_prev + ((-1) * w.max_acc) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dock_prev + ((-1) * w.max_acc) + (w.locality * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dock_prev + ((-1) * w.max_acc) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.rightmost * l)) ∧
  0 < (w.dep_acc + w.dock_prev + w.float) ∧
  0 < (w.dep_acc + w.dock_prev + w.float + w.max_acc) ∧
  0 < (w.dep_acc + w.dock_prev + w.float + w.max_acc + (w.nonfinal * l)) ∧
  0 < (w.dep_acc + w.dock_prev + w.float + w.max_acc + (w.osd * l) + (w.rightmost * l)) ∧
  0 < (w.dep_acc + w.dock_prev + w.float + (w.nonfinal * l)) ∧
  0 < (w.dep_acc + w.dock_prev + w.float + (w.osd * l) + (w.rightmost * l)) ∧
  0 < (w.dep_acc + w.dock_prev + w.float + ((-1) * w.maxlink) + (w.nonfinal * l)) ∧
  0 < (w.dep_acc + w.dock_prev + w.float + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.nonfinal * l)) ∧
  0 < (w.dep_acc + w.dock_prev + w.float + (w.float * l)) ∧
  0 < (w.dep_acc + w.dock_prev + w.float + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (w.dep_acc + w.dock_prev + w.float + (w.float * l) + (w.osd * l) + (w.rightmost * l)) ∧
  0 < (w.dep_acc + w.dock_prev + w.float + ((-1) * w.max_acc) + (w.float * l)) ∧
  0 < (w.dep_acc + w.dock_prev + w.float + ((-1) * w.max_acc) + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (w.dep_acc + w.dock_prev + w.float + ((-1) * w.max_acc) + (w.float * l) + (w.osd * l) + (w.rightmost * l)) ∧
  0 < w.dock_prev ∧
  0 < (w.dock_prev + w.float + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.dock_prev + w.float + ((-1) * w.max_acc) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.dock_prev + w.float + (w.osd * l) + (w.rightmost * l)) ∧
  0 < (w.dock_prev + w.float + ((-1) * w.max_acc) + (w.osd * l) + (w.rightmost * l)) ∧
  0 < (w.dock_prev + ((-1) * w.max_acc) + (w.float * l)) ∧
  0 < (w.dock_prev + ((-1) * w.max_acc) + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (w.dock_prev + ((-1) * w.max_acc) + (w.float * l) + (w.osd * l) + (w.rightmost * l)) ∧
  0 < (w.dock_prev + (w.nonfinal * l)) ∧
  0 < (w.dock_prev + (w.osd * l) + (w.rightmost * l)) ∧
  0 < (w.dock_prev + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.nonfinal * l))
def spring_loc_1 (w : Weights) (l : ℝ) : Prop :=
  0 < (w.dock_prev + w.float + w.max_acc + ((-1) * w.deplink) + (w.osd * l)) ∧
  0 < (w.dock_prev + w.float + ((-1) * w.deplink) + (w.osd * l)) ∧
  0 < (w.dock_prev + w.float + ((-1) * w.deplink) + (2 * w.max_acc) + (w.osd * l) + ((-1) * w.float * l)) ∧
  0 < (w.dock_prev + w.float + w.max_acc + ((-1) * w.deplink) + (w.osd * l) + ((-1) * w.float * l)) ∧
  0 < (w.dock_prev + w.float + ((-1) * w.deplink) + ((-1) * w.maxlink) + ((-1) * w.float * l)) ∧
  0 < (w.dock_prev + w.float + w.max_acc + ((-1) * w.deplink) + ((-1) * w.maxlink) + ((-1) * w.float * l)) ∧
  0 < (w.dep_acc + w.dock_prev + (2 * w.deplink) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l) + (2 * w.clash * l)) ∧
  0 < (w.dep_acc + w.dock_prev + (2 * w.deplink) + (w.locality * l) + (w.rightmost * l) + ((-1) * w.float * l) + (2 * w.clash * l)) ∧
  0 < (w.dep_acc + w.dock_prev + (2 * w.deplink) + (w.rightmost * l) + ((-1) * w.float * l) + (2 * w.clash * l)) ∧
  0 < (w.dep_acc + (2 * w.deplink) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l) + (2 * w.clash * l)) ∧
  0 < (w.dep_acc + (2 * w.deplink) + (w.rightmost * l) + ((-1) * w.float * l) + (2 * w.clash * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + ((-1) * w.maxlink) + (w.nonfinal * l) + ((-1) * w.float * l) + (2 * w.clash * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + ((-1) * w.maxlink) + (w.rightmost * l) + ((-1) * w.float * l) + (2 * w.clash * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.maxlink) + (w.nonfinal * l) + ((-1) * w.float * l) + (2 * w.clash * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.maxlink) + (w.rightmost * l) + ((-1) * w.float * l) + (2 * w.clash * l)) ∧
  0 < (w.dep_acc + w.dock_prev + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.dep_acc + w.dock_prev + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.dep_acc + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.dep_acc + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.clash * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + (w.clash * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + (w.clash * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + w.float + (w.clash * l) + (w.locality * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + w.float + w.max_acc + (w.clash * l) + (w.locality * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + w.float + w.max_acc + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + w.float + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + w.float + w.max_acc + (w.clash * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + w.float + (w.clash * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + w.max_acc + (w.clash * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + w.max_acc + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + w.max_acc + (w.clash * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + ((-1) * w.maxlink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dep_acc + w.max_acc + (w.clash * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.dep_acc + w.max_acc + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.dock_prev + (w.clash * l) + (w.locality * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.dock_prev + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.dock_prev + (w.clash * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.dep_acc + w.dock_prev + w.float + ((-1) * w.maxlink) + (w.clash * l) + ((-1) * w.float * l)) ∧
  0 < (w.dep_acc + w.dock_prev + w.float + w.max_acc + ((-1) * w.maxlink) + (w.clash * l) + ((-1) * w.float * l)) ∧
  0 < (w.dep_acc + w.dock_prev + w.float + w.max_acc + ((-1) * w.maxlink) + (w.clash * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.dep_acc + w.dock_prev + w.float + ((-1) * w.maxlink) + (w.clash * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.dock_prev + ((-1) * w.maxlink) + (w.clash * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.maxlink) + (w.clash * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + w.float + w.max_acc + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + w.float + w.max_acc + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + w.float + w.max_acc + (w.locality * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + w.float + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + w.float + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + w.float + (w.locality * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + w.float + w.max_acc + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + w.float + w.max_acc + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + w.float + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + w.float + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + w.max_acc + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + w.max_acc + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.dep_acc + w.dock_prev + w.max_acc + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dep_acc + w.max_acc + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.dock_prev + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.dock_prev + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.dock_prev + (w.locality * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.dock_prev + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.dep_acc + w.dock_prev + w.float) ∧
  0 < (w.dep_acc + w.dock_prev + w.float + w.max_acc) ∧
  0 < (w.dep_acc + w.dock_prev + w.float + w.max_acc + (w.nonfinal * l)) ∧
  0 < (w.dep_acc + w.dock_prev + w.float + w.max_acc + (w.osd * l) + (w.rightmost * l)) ∧
  0 < (w.dep_acc + w.dock_prev + w.float + (w.nonfinal * l)) ∧
  0 < (w.dep_acc + w.dock_prev + w.float + (w.osd * l) + (w.rightmost * l)) ∧
  0 < (w.dep_acc + w.dock_prev + w.float + (2 * w.max_acc) + ((-1) * w.float * l)) ∧
  0 < (w.dep_acc + w.dock_prev + w.float + (2 * w.max_acc) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.dep_acc + w.dock_prev + w.float + (2 * w.max_acc) + (w.osd * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.dep_acc + w.dock_prev + w.float + w.max_acc + ((-1) * w.float * l)) ∧
  0 < (w.dep_acc + w.dock_prev + w.float + w.max_acc + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.dep_acc + w.dock_prev + w.float + w.max_acc + (w.osd * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.dep_acc + w.dock_prev + w.float + w.max_acc + ((-1) * w.maxlink) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.dep_acc + w.dock_prev + w.float + ((-1) * w.maxlink) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < w.dock_prev ∧
  0 < (w.dock_prev + (w.nonfinal * l)) ∧
  0 < (w.dock_prev + (w.osd * l) + (w.rightmost * l)) ∧
  0 < (w.dock_prev + w.float + w.max_acc + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.dock_prev + w.float + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.dock_prev + w.float + w.max_acc + (w.osd * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.dock_prev + w.float + (w.osd * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.dock_prev + w.max_acc + ((-1) * w.float * l)) ∧
  0 < (w.dock_prev + w.max_acc + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.dock_prev + w.max_acc + (w.osd * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.dock_prev + ((-1) * w.maxlink) + (w.nonfinal * l) + ((-1) * w.float * l))
def spring_loc_2 (w : Weights) (l : ℝ) : Prop :=
  0 < (w.max_acc + ((-1) * w.deplink) + (w.float * l) + (w.osd * l) + ((-1) * w.locality * l)) ∧
  0 < (((-1) * w.deplink) + (w.float * l) + (w.osd * l) + ((-1) * w.locality * l)) ∧
  0 < (((-1) * w.deplink) + (2 * w.max_acc) + (w.osd * l) + ((-1) * w.locality * l)) ∧
  0 < (w.max_acc + ((-1) * w.deplink) + (w.osd * l) + ((-1) * w.locality * l)) ∧
  0 < (((-1) * w.deplink) + ((-1) * w.maxlink) + ((-1) * w.locality * l)) ∧
  0 < (w.max_acc + ((-1) * w.deplink) + ((-1) * w.maxlink) + ((-1) * w.locality * l)) ∧
  0 < (w.max_acc + ((-1) * w.float) + ((-1) * w.locality * l)) ∧
  0 < (w.max_acc + ((-1) * w.float) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.max_acc + ((-1) * w.float) + (w.osd * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (((-1) * w.float) + ((-1) * w.maxlink) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.max_acc + (w.osd * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + ((-1) * w.dock_prev) + ((-1) * w.float) + (2 * w.deplink) + (w.nonfinal * l) + (2 * w.clash * l)) ∧
  0 < (w.dep_acc + ((-1) * w.dock_prev) + ((-1) * w.float) + (2 * w.deplink) + (w.rightmost * l) + ((-1) * w.locality * l) + (2 * w.clash * l)) ∧
  0 < (w.dep_acc + ((-1) * w.float) + (2 * w.deplink) + (w.nonfinal * l) + (2 * w.clash * l)) ∧
  0 < (w.dep_acc + ((-1) * w.float) + (2 * w.deplink) + (w.rightmost * l) + (2 * w.clash * l)) ∧
  0 < (w.dep_acc + ((-1) * w.float) + (2 * w.deplink) + (w.rightmost * l) + ((-1) * w.locality * l) + (2 * w.clash * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.dock_prev) + ((-1) * w.float) + ((-1) * w.maxlink) + (w.nonfinal * l) + ((-1) * w.locality * l) + (2 * w.clash * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.dock_prev) + ((-1) * w.float) + ((-1) * w.maxlink) + (w.rightmost * l) + ((-1) * w.locality * l) + (2 * w.clash * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.float) + ((-1) * w.maxlink) + (w.nonfinal * l) + ((-1) * w.locality * l) + (2 * w.clash * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.float) + ((-1) * w.maxlink) + (w.rightmost * l) + ((-1) * w.locality * l) + (2 * w.clash * l)) ∧
  0 < (w.dep_acc + ((-1) * w.dock_prev) + ((-1) * w.float) + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.dep_acc + ((-1) * w.dock_prev) + ((-1) * w.float) + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + ((-1) * w.float) + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.dep_acc + ((-1) * w.float) + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.clash * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.float) + (w.clash * l) + (w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.float) + (w.clash * l) + (w.float * l) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.float) + (w.clash * l) + (w.float * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + w.max_acc + (w.clash * l)) ∧
  0 < (w.deplink + w.dep_acc + w.max_acc + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.dock_prev) + ((-1) * w.float) + (w.clash * l) + (w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.dock_prev) + ((-1) * w.float) + (w.clash * l) + (w.float * l) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + w.max_acc + ((-1) * w.dock_prev) + ((-1) * w.float) + (w.clash * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + w.max_acc + ((-1) * w.dock_prev) + ((-1) * w.float) + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + w.max_acc + ((-1) * w.float) + (w.clash * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + w.max_acc + ((-1) * w.float) + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + w.max_acc + ((-1) * w.float) + (w.clash * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.float) + ((-1) * w.maxlink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + w.max_acc + (w.clash * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.clash * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + ((-1) * w.dock_prev) + ((-1) * w.float) + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + (w.clash * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + (w.clash * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + ((-1) * w.maxlink) + (w.clash * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + w.max_acc + ((-1) * w.maxlink) + (w.clash * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + w.max_acc + ((-1) * w.maxlink) + (w.clash * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + ((-1) * w.maxlink) + (w.clash * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (((-1) * w.dock_prev) + ((-1) * w.float) + ((-1) * w.maxlink) + (w.clash * l) + ((-1) * w.locality * l)) ∧
  0 < (((-1) * w.float) + ((-1) * w.maxlink) + (w.clash * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.float) + (w.float * l) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.float) + (w.float * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.float) + (w.float * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + w.max_acc + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dep_acc + w.max_acc + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dep_acc + w.max_acc + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.dock_prev) + ((-1) * w.float) + (w.float * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + w.max_acc + ((-1) * w.dock_prev) + ((-1) * w.float) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + w.max_acc + ((-1) * w.float) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + w.max_acc + ((-1) * w.float) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + w.max_acc + ((-1) * w.float) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + w.max_acc + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + w.max_acc + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + ((-1) * w.dock_prev) + ((-1) * w.float) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + (w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + w.max_acc + (w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + w.max_acc + (w.float * l) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + w.max_acc + (w.float * l) + (w.osd * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + (w.float * l) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + (w.float * l) + (w.osd * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + (2 * w.max_acc) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + (2 * w.max_acc) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + (2 * w.max_acc) + (w.osd * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + w.max_acc + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + w.max_acc + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + w.max_acc + (w.osd * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + w.max_acc + ((-1) * w.maxlink) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + ((-1) * w.maxlink) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (((-1) * w.float) + (w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (((-1) * w.float) + (w.float * l) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (((-1) * w.float) + (w.float * l) + (w.osd * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.max_acc + (w.nonfinal * l)) ∧
  0 < (w.nonfinal * l) ∧
  0 < ((w.osd * l) + (w.rightmost * l) + ((-1) * w.locality * l))
def spring_loc_3 (w : Weights) (l : ℝ) : Prop :=
  0 < (((-1) * w.deplink) + (w.float * l) + (w.osd * l) + ((-1) * w.locality * l)) ∧
  0 < (((-1) * w.deplink) + ((-1) * w.max_acc) + (w.float * l) + (w.osd * l) + ((-1) * w.locality * l)) ∧
  0 < (w.max_acc + ((-1) * w.deplink) + (w.osd * l) + ((-1) * w.locality * l)) ∧
  0 < (((-1) * w.deplink) + (w.osd * l) + ((-1) * w.locality * l)) ∧
  0 < (((-1) * w.deplink) + ((-1) * w.maxlink) + ((-1) * w.locality * l)) ∧
  0 < (((-1) * w.deplink) + ((-1) * w.maxlink) + ((-1) * w.max_acc) + ((-1) * w.locality * l)) ∧
  0 < (((-1) * w.float) + ((-1) * w.locality * l)) ∧
  0 < (((-1) * w.float) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (((-1) * w.float) + (w.osd * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (((-1) * w.float) + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (((-1) * w.max_acc) + (w.osd * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (((-1) * w.max_acc) + (w.nonfinal * l)) ∧
  0 < (w.dep_acc + ((-1) * w.dock_prev) + ((-1) * w.float) + ((-1) * w.max_acc) + (2 * w.deplink) + (w.rightmost * l) + ((-1) * w.locality * l) + (2 * w.clash * l)) ∧
  0 < (w.dep_acc + ((-1) * w.dock_prev) + ((-1) * w.float) + ((-1) * w.max_acc) + (2 * w.deplink) + (w.nonfinal * l) + (2 * w.clash * l)) ∧
  0 < (w.dep_acc + ((-1) * w.float) + ((-1) * w.max_acc) + (2 * w.deplink) + (w.rightmost * l) + ((-1) * w.locality * l) + (2 * w.clash * l)) ∧
  0 < (w.dep_acc + ((-1) * w.float) + ((-1) * w.max_acc) + (2 * w.deplink) + (w.nonfinal * l) + (2 * w.clash * l)) ∧
  0 < (w.dep_acc + ((-1) * w.float) + ((-1) * w.max_acc) + (2 * w.deplink) + (w.rightmost * l) + (2 * w.clash * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.dock_prev) + ((-1) * w.float) + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.nonfinal * l) + ((-1) * w.locality * l) + (2 * w.clash * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.dock_prev) + ((-1) * w.float) + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.rightmost * l) + ((-1) * w.locality * l) + (2 * w.clash * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.float) + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.nonfinal * l) + ((-1) * w.locality * l) + (2 * w.clash * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.float) + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.rightmost * l) + ((-1) * w.locality * l) + (2 * w.clash * l)) ∧
  0 < (w.dep_acc + ((-1) * w.dock_prev) + ((-1) * w.float) + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + ((-1) * w.dock_prev) + ((-1) * w.float) + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.dep_acc + ((-1) * w.float) + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + ((-1) * w.float) + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.clash * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.float) + ((-1) * w.max_acc) + (w.clash * l) + (w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.float) + ((-1) * w.max_acc) + (w.clash * l) + (w.float * l) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.float) + ((-1) * w.max_acc) + (w.clash * l) + (w.float * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.dock_prev) + ((-1) * w.float) + ((-1) * w.max_acc) + (w.clash * l) + (w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.dock_prev) + ((-1) * w.float) + ((-1) * w.max_acc) + (w.clash * l) + (w.float * l) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.dock_prev) + ((-1) * w.float) + (w.clash * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.dock_prev) + ((-1) * w.float) + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.float) + (w.clash * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.float) + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.float) + (w.clash * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.float) + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.clash * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.max_acc) + (w.clash * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.max_acc) + (w.clash * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.max_acc) + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-1) * w.dock_prev) + ((-1) * w.float) + ((-1) * w.max_acc) + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + ((-1) * w.max_acc) + (w.clash * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + ((-1) * w.max_acc) + (w.clash * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + ((-1) * w.max_acc) + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (w.dep_acc + ((-1) * w.maxlink) + (w.clash * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + ((-1) * w.maxlink) + (w.clash * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (((-1) * w.dock_prev) + ((-1) * w.float) + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + ((-1) * w.locality * l)) ∧
  0 < (((-1) * w.float) + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.float) + ((-1) * w.max_acc) + (w.float * l) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.float) + ((-1) * w.max_acc) + (w.float * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.float) + ((-1) * w.max_acc) + (w.float * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.dock_prev) + ((-1) * w.float) + ((-1) * w.max_acc) + (w.float * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.dock_prev) + ((-1) * w.float) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.float) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.float) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.float) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.max_acc) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.max_acc) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.max_acc) + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.max_acc) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.dep_acc + ((-1) * w.max_acc) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.dock_prev) + ((-1) * w.float) + ((-1) * w.max_acc) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + ((-1) * w.max_acc) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + ((-1) * w.max_acc) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + ((-1) * w.max_acc) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + ((-1) * w.max_acc) + (w.rightmost * l)) ∧
  0 < (w.dep_acc + (w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + (w.float * l) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + (w.float * l) + (w.osd * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + ((-1) * w.max_acc) + (w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + ((-1) * w.max_acc) + (w.float * l) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + ((-1) * w.max_acc) + (w.float * l) + (w.osd * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + w.max_acc + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + w.max_acc + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + w.max_acc + (w.osd * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + (w.osd * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + ((-1) * w.maxlink) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (w.dep_acc + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (((-1) * w.float) + ((-1) * w.max_acc) + (w.float * l) + ((-1) * w.locality * l)) ∧
  0 < (((-1) * w.float) + ((-1) * w.max_acc) + (w.float * l) + (w.nonfinal * l) + ((-1) * w.locality * l)) ∧
  0 < (((-1) * w.float) + ((-1) * w.max_acc) + (w.float * l) + (w.osd * l) + (w.rightmost * l) + ((-1) * w.locality * l)) ∧
  0 < (w.nonfinal * l) ∧
  0 < ((w.osd * l) + (w.rightmost * l) + ((-1) * w.locality * l))
def spring_loc_4 (w : Weights) (l : ℝ) : Prop :=
  0 < (((-1) * w.deplink) + ((-1) * w.dep_acc) + (w.float * l) + (w.osd * l)) ∧
  0 < (((-1) * w.deplink) + ((-1) * w.dep_acc) + ((-1) * w.max_acc) + (w.float * l) + (w.osd * l)) ∧
  0 < (w.max_acc + ((-1) * w.deplink) + ((-1) * w.dep_acc) + (w.osd * l)) ∧
  0 < (((-1) * w.deplink) + ((-1) * w.dep_acc) + (w.osd * l)) ∧
  0 < (((-1) * w.deplink) + ((-1) * w.dep_acc) + ((-1) * w.maxlink)) ∧
  0 < (((-1) * w.deplink) + ((-1) * w.dep_acc) + ((-1) * w.maxlink) + ((-1) * w.max_acc)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.float) + ((-1) * w.max_acc) + (w.float * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.float) + ((-1) * w.max_acc) + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.float) + ((-1) * w.max_acc) + (w.float * l) + (w.osd * l) + (w.rightmost * l)) ∧
  0 < (((-1) * w.dep_acc) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.max_acc) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (((-1) * w.dep_acc) + (w.osd * l) + (w.rightmost * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.float)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.float) + (w.nonfinal * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.float) + (w.osd * l) + (w.rightmost * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.float) + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.nonfinal * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.max_acc) + (w.osd * l) + (w.rightmost * l)) ∧
  0 < (((-1) * w.maxlink) + (w.nonfinal * l)) ∧
  0 < (((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.nonfinal * l)) ∧
  0 < 0 ∧
  0 < (((-1) * w.dock_prev) + ((-1) * w.float) + ((-1) * w.max_acc) + (2 * w.deplink) + (w.locality * l) + (w.nonfinal * l) + (2 * w.clash * l)) ∧
  0 < (((-1) * w.dock_prev) + ((-1) * w.float) + ((-1) * w.max_acc) + (2 * w.deplink) + (w.rightmost * l) + (2 * w.clash * l)) ∧
  0 < (((-1) * w.float) + ((-1) * w.max_acc) + (2 * w.deplink) + (w.locality * l) + (w.nonfinal * l) + (2 * w.clash * l)) ∧
  0 < (((-1) * w.float) + ((-1) * w.max_acc) + (2 * w.deplink) + (w.locality * l) + (w.rightmost * l) + (2 * w.clash * l)) ∧
  0 < (((-1) * w.float) + ((-1) * w.max_acc) + (2 * w.deplink) + (w.rightmost * l) + (2 * w.clash * l)) ∧
  0 < (w.deplink + ((-1) * w.dock_prev) + ((-1) * w.float) + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.nonfinal * l) + (2 * w.clash * l)) ∧
  0 < (w.deplink + ((-1) * w.dock_prev) + ((-1) * w.float) + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.rightmost * l) + (2 * w.clash * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.nonfinal * l) + (2 * w.clash * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.rightmost * l) + (2 * w.clash * l)) ∧
  0 < (((-1) * w.dock_prev) + ((-1) * w.float) + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (((-1) * w.dock_prev) + ((-1) * w.float) + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (((-1) * w.float) + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (((-1) * w.float) + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + ((-1) * w.max_acc) + (w.clash * l) + (w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + ((-1) * w.max_acc) + (w.clash * l) + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + ((-1) * w.max_acc) + (w.clash * l) + (w.float * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + (w.clash * l) + (w.locality * l)) ∧
  0 < (w.deplink + (w.clash * l) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.clash * l) + (w.locality * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + (w.clash * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + ((-1) * w.dock_prev) + ((-1) * w.float) + ((-1) * w.max_acc) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + ((-1) * w.float) + ((-1) * w.max_acc) + (w.clash * l) + (w.locality * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + ((-1) * w.float) + ((-1) * w.max_acc) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + ((-1) * w.float) + ((-1) * w.max_acc) + (w.clash * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.dock_prev) + ((-1) * w.float) + ((-1) * w.max_acc) + (w.clash * l) + (w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.dock_prev) + ((-1) * w.float) + ((-1) * w.max_acc) + (w.clash * l) + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-1) * w.dock_prev) + ((-1) * w.float) + (w.clash * l)) ∧
  0 < (w.deplink + ((-1) * w.dock_prev) + ((-1) * w.float) + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + (w.clash * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + (w.clash * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.clash * l) + (w.rightmost * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.dock_prev) + ((-1) * w.float) + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.float) + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + (w.rightmost * l)) ∧
  0 < (((-1) * w.maxlink) + (w.clash * l)) ∧
  0 < (((-1) * w.maxlink) + (w.clash * l) + (w.rightmost * l)) ∧
  0 < (((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l)) ∧
  0 < (((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + ((-1) * w.max_acc) + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + ((-1) * w.max_acc) + (w.float * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + ((-1) * w.max_acc) + (w.float * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + (w.locality * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.locality * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + ((-1) * w.dock_prev) + ((-1) * w.float) + ((-1) * w.max_acc) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + ((-1) * w.float) + ((-1) * w.max_acc) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + ((-1) * w.float) + ((-1) * w.max_acc) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + ((-1) * w.float) + ((-1) * w.max_acc) + (w.locality * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + ((-1) * w.float) + ((-1) * w.max_acc) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.dock_prev) + ((-1) * w.float) + ((-1) * w.max_acc) + (w.float * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.dock_prev) + ((-1) * w.float) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.rightmost * l)) ∧
  0 < (w.float * l) ∧
  0 < (((-1) * w.max_acc) + (w.float * l)) ∧
  0 < (((-1) * w.max_acc) + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (((-1) * w.max_acc) + (w.float * l) + (w.osd * l) + (w.rightmost * l)) ∧
  0 < w.max_acc ∧
  0 < (w.max_acc + (w.nonfinal * l)) ∧
  0 < (w.max_acc + (w.osd * l) + (w.rightmost * l)) ∧
  0 < (w.nonfinal * l) ∧
  0 < ((w.float * l) + (w.nonfinal * l)) ∧
  0 < ((w.float * l) + (w.osd * l) + (w.rightmost * l)) ∧
  0 < ((w.osd * l) + (w.rightmost * l))
def spring_loc_5 (w : Weights) (l : ℝ) : Prop :=
  0 < (((-1) * w.deplink) + ((-1) * w.dep_acc) + ((-2) * w.max_acc) + (w.float * l) + (w.osd * l)) ∧
  0 < (((-1) * w.deplink) + ((-1) * w.dep_acc) + ((-1) * w.max_acc) + (w.float * l) + (w.osd * l)) ∧
  0 < (((-1) * w.deplink) + ((-1) * w.dep_acc) + (w.osd * l)) ∧
  0 < (((-1) * w.deplink) + ((-1) * w.dep_acc) + ((-1) * w.maxlink) + ((-2) * w.max_acc)) ∧
  0 < (((-1) * w.deplink) + ((-1) * w.dep_acc) + ((-1) * w.maxlink) + ((-1) * w.max_acc)) ∧
  0 < (((-1) * w.deplink) + ((-1) * w.dep_acc) + ((-1) * w.max_acc) + (w.osd * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.float) + ((-2) * w.max_acc) + (w.float * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.float) + ((-2) * w.max_acc) + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.float) + ((-2) * w.max_acc) + (w.float * l) + (w.osd * l) + (w.rightmost * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-2) * w.max_acc) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.max_acc) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-2) * w.max_acc) + (w.osd * l) + (w.rightmost * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.float) + ((-1) * w.maxlink) + ((-2) * w.max_acc) + (w.nonfinal * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.float) + ((-1) * w.max_acc)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.float) + ((-1) * w.max_acc) + (w.nonfinal * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.float) + ((-1) * w.max_acc) + (w.osd * l) + (w.rightmost * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.max_acc) + (w.osd * l) + (w.rightmost * l)) ∧
  0 < (((-1) * w.maxlink) + ((-2) * w.max_acc) + (w.nonfinal * l)) ∧
  0 < (((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.nonfinal * l)) ∧
  0 < ((-1) * w.max_acc) ∧
  0 < (((-1) * w.max_acc) + (w.nonfinal * l)) ∧
  0 < (((-1) * w.max_acc) + (w.osd * l) + (w.rightmost * l)) ∧
  0 < 0 ∧
  0 < (((-1) * w.dock_prev) + ((-1) * w.float) + ((-2) * w.max_acc) + (2 * w.deplink) + (w.locality * l) + (w.nonfinal * l) + (2 * w.clash * l)) ∧
  0 < (((-1) * w.dock_prev) + ((-1) * w.float) + ((-2) * w.max_acc) + (2 * w.deplink) + (w.rightmost * l) + (2 * w.clash * l)) ∧
  0 < (((-1) * w.float) + ((-2) * w.max_acc) + (2 * w.deplink) + (w.locality * l) + (w.nonfinal * l) + (2 * w.clash * l)) ∧
  0 < (((-1) * w.float) + ((-2) * w.max_acc) + (2 * w.deplink) + (w.locality * l) + (w.rightmost * l) + (2 * w.clash * l)) ∧
  0 < (((-1) * w.float) + ((-2) * w.max_acc) + (2 * w.deplink) + (w.rightmost * l) + (2 * w.clash * l)) ∧
  0 < (w.deplink + ((-1) * w.dock_prev) + ((-1) * w.float) + ((-1) * w.maxlink) + ((-2) * w.max_acc) + (w.nonfinal * l) + (2 * w.clash * l)) ∧
  0 < (w.deplink + ((-1) * w.dock_prev) + ((-1) * w.float) + ((-1) * w.maxlink) + ((-2) * w.max_acc) + (w.rightmost * l) + (2 * w.clash * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + ((-1) * w.maxlink) + ((-2) * w.max_acc) + (w.nonfinal * l) + (2 * w.clash * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + ((-1) * w.maxlink) + ((-2) * w.max_acc) + (w.rightmost * l) + (2 * w.clash * l)) ∧
  0 < (((-1) * w.dock_prev) + ((-1) * w.float) + ((-2) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (((-1) * w.dock_prev) + ((-1) * w.float) + ((-2) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (((-1) * w.float) + ((-2) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (((-1) * w.float) + ((-2) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + ((-2) * w.max_acc) + (w.clash * l) + (w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + ((-2) * w.max_acc) + (w.clash * l) + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + ((-2) * w.max_acc) + (w.clash * l) + (w.float * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-2) * w.max_acc) + (w.clash * l) + (w.locality * l)) ∧
  0 < (w.deplink + ((-2) * w.max_acc) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.clash * l) + (w.locality * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-2) * w.max_acc) + (w.clash * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + ((-1) * w.dock_prev) + ((-1) * w.float) + ((-2) * w.max_acc) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + ((-1) * w.float) + ((-2) * w.max_acc) + (w.clash * l) + (w.locality * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + ((-1) * w.float) + ((-2) * w.max_acc) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + ((-1) * w.float) + ((-2) * w.max_acc) + (w.clash * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.dock_prev) + ((-1) * w.float) + ((-2) * w.max_acc) + (w.clash * l) + (w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.dock_prev) + ((-1) * w.float) + ((-2) * w.max_acc) + (w.clash * l) + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-1) * w.dock_prev) + ((-1) * w.float) + ((-1) * w.max_acc) + (w.clash * l)) ∧
  0 < (w.deplink + ((-1) * w.dock_prev) + ((-1) * w.float) + ((-1) * w.max_acc) + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + ((-1) * w.maxlink) + ((-2) * w.max_acc) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + ((-1) * w.max_acc) + (w.clash * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + ((-1) * w.max_acc) + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + ((-1) * w.max_acc) + (w.clash * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.clash * l) + (w.rightmost * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.dock_prev) + ((-1) * w.float) + ((-1) * w.maxlink) + ((-2) * w.max_acc) + (w.clash * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.float) + ((-1) * w.maxlink) + ((-2) * w.max_acc) + (w.clash * l) + (w.rightmost * l)) ∧
  0 < (((-1) * w.maxlink) + ((-2) * w.max_acc) + (w.clash * l)) ∧
  0 < (((-1) * w.maxlink) + ((-2) * w.max_acc) + (w.clash * l) + (w.rightmost * l)) ∧
  0 < (((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l)) ∧
  0 < (((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + ((-2) * w.max_acc) + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + ((-2) * w.max_acc) + (w.float * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + ((-2) * w.max_acc) + (w.float * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-2) * w.max_acc) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-2) * w.max_acc) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-2) * w.max_acc) + (w.locality * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.locality * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-2) * w.max_acc) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-2) * w.max_acc) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + ((-1) * w.dock_prev) + ((-1) * w.float) + ((-2) * w.max_acc) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + ((-1) * w.float) + ((-2) * w.max_acc) + (w.locality * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + ((-1) * w.float) + ((-2) * w.max_acc) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + ((-1) * w.float) + ((-2) * w.max_acc) + (w.locality * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + ((-1) * w.float) + ((-2) * w.max_acc) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.dock_prev) + ((-1) * w.float) + ((-2) * w.max_acc) + (w.float * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.dock_prev) + ((-1) * w.float) + ((-1) * w.max_acc) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + ((-1) * w.max_acc) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + ((-1) * w.max_acc) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + ((-1) * w.max_acc) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.rightmost * l)) ∧
  0 < (((-2) * w.max_acc) + (w.float * l)) ∧
  0 < (((-2) * w.max_acc) + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (((-2) * w.max_acc) + (w.float * l) + (w.osd * l) + (w.rightmost * l)) ∧
  0 < (((-1) * w.max_acc) + (w.float * l)) ∧
  0 < (((-1) * w.max_acc) + (w.float * l) + (w.nonfinal * l)) ∧
  0 < (((-1) * w.max_acc) + (w.float * l) + (w.osd * l) + (w.rightmost * l)) ∧
  0 < (w.nonfinal * l) ∧
  0 < ((w.osd * l) + (w.rightmost * l))
def spring_loc_6 (w : Weights) (l : ℝ) : Prop :=
  0 < (w.max_acc + ((-1) * w.deplink) + ((-1) * w.dep_acc) + (w.osd * l)) ∧
  0 < (((-1) * w.deplink) + ((-1) * w.dep_acc) + (w.osd * l)) ∧
  0 < (((-1) * w.deplink) + ((-1) * w.dep_acc) + (2 * w.max_acc) + (w.osd * l) + ((-1) * w.float * l)) ∧
  0 < (w.max_acc + ((-1) * w.deplink) + ((-1) * w.dep_acc) + (w.osd * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.deplink) + ((-1) * w.dep_acc) + ((-1) * w.maxlink) + ((-1) * w.float * l)) ∧
  0 < (w.max_acc + ((-1) * w.deplink) + ((-1) * w.dep_acc) + ((-1) * w.maxlink) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.float)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.float) + (w.nonfinal * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.float) + (w.osd * l) + (w.rightmost * l)) ∧
  0 < (w.max_acc + ((-1) * w.dep_acc) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.dep_acc) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.max_acc + ((-1) * w.dep_acc) + (w.osd * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.dep_acc) + (w.osd * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.max_acc + ((-1) * w.dep_acc) + ((-1) * w.float) + ((-1) * w.float * l)) ∧
  0 < (w.max_acc + ((-1) * w.dep_acc) + ((-1) * w.float) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.max_acc + ((-1) * w.dep_acc) + ((-1) * w.float) + (w.osd * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.float) + ((-1) * w.maxlink) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < ((2 * w.max_acc) + ((-1) * w.float * l)) ∧
  0 < ((2 * w.max_acc) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < ((2 * w.max_acc) + (w.osd * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.max_acc + ((-1) * w.float * l)) ∧
  0 < (w.max_acc + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.max_acc + (w.osd * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.max_acc + ((-1) * w.maxlink) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.maxlink) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < 0 ∧
  0 < (((-1) * w.dock_prev) + ((-1) * w.float) + (2 * w.deplink) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l) + (2 * w.clash * l)) ∧
  0 < (((-1) * w.dock_prev) + ((-1) * w.float) + (2 * w.deplink) + (w.rightmost * l) + ((-1) * w.float * l) + (2 * w.clash * l)) ∧
  0 < (((-1) * w.float) + (2 * w.deplink) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l) + (2 * w.clash * l)) ∧
  0 < (((-1) * w.float) + (2 * w.deplink) + (w.locality * l) + (w.rightmost * l) + ((-1) * w.float * l) + (2 * w.clash * l)) ∧
  0 < (((-1) * w.float) + (2 * w.deplink) + (w.rightmost * l) + ((-1) * w.float * l) + (2 * w.clash * l)) ∧
  0 < (w.deplink + ((-1) * w.dock_prev) + ((-1) * w.float) + ((-1) * w.maxlink) + (w.nonfinal * l) + ((-1) * w.float * l) + (2 * w.clash * l)) ∧
  0 < (w.deplink + ((-1) * w.dock_prev) + ((-1) * w.float) + ((-1) * w.maxlink) + (w.rightmost * l) + ((-1) * w.float * l) + (2 * w.clash * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + ((-1) * w.maxlink) + (w.nonfinal * l) + ((-1) * w.float * l) + (2 * w.clash * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + ((-1) * w.maxlink) + (w.rightmost * l) + ((-1) * w.float * l) + (2 * w.clash * l)) ∧
  0 < (((-1) * w.dock_prev) + ((-1) * w.float) + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.dock_prev) + ((-1) * w.float) + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.float) + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.float) + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + ((-1) * w.dock_prev) + ((-1) * w.float) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + ((-1) * w.float) + (w.clash * l) + (w.locality * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + ((-1) * w.float) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + ((-1) * w.float) + (w.clash * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.dock_prev) + ((-1) * w.float) + (w.clash * l)) ∧
  0 < (w.deplink + ((-1) * w.dock_prev) + ((-1) * w.float) + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + w.max_acc + ((-1) * w.dock_prev) + ((-1) * w.float) + (w.clash * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.max_acc + ((-1) * w.dock_prev) + ((-1) * w.float) + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + (w.clash * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + (w.clash * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + (w.clash * l) + (w.locality * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.max_acc + (w.clash * l) + (w.locality * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.max_acc + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.max_acc + (w.clash * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.clash * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.max_acc + ((-1) * w.float) + (w.clash * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.max_acc + ((-1) * w.float) + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.max_acc + ((-1) * w.float) + (w.clash * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + ((-1) * w.maxlink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.dock_prev) + ((-1) * w.float) + ((-1) * w.maxlink) + (w.clash * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.float) + ((-1) * w.maxlink) + (w.clash * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.maxlink) + (w.clash * l) + ((-1) * w.float * l)) ∧
  0 < (w.max_acc + ((-1) * w.maxlink) + (w.clash * l) + ((-1) * w.float * l)) ∧
  0 < (w.max_acc + ((-1) * w.maxlink) + (w.clash * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.maxlink) + (w.clash * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + ((-1) * w.dock_prev) + ((-1) * w.float) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + ((-1) * w.float) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + ((-1) * w.float) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + ((-1) * w.float) + (w.locality * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + ((-1) * w.float) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.dock_prev) + ((-1) * w.float) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.max_acc + ((-1) * w.dock_prev) + ((-1) * w.float) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + (w.rightmost * l)) ∧
  0 < (w.deplink + w.max_acc + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.max_acc + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.max_acc + (w.locality * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.locality * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.max_acc + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.max_acc + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.max_acc + ((-1) * w.float) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.max_acc + ((-1) * w.float) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + w.max_acc + ((-1) * w.float) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < w.max_acc ∧
  0 < (w.max_acc + (w.nonfinal * l)) ∧
  0 < (w.max_acc + (w.osd * l) + (w.rightmost * l)) ∧
  0 < (w.nonfinal * l) ∧
  0 < ((w.osd * l) + (w.rightmost * l))
def spring_loc_7 (w : Weights) (l : ℝ) : Prop :=
  0 < (((-1) * w.deplink) + ((-1) * w.dep_acc) + (w.osd * l)) ∧
  0 < (w.max_acc + ((-1) * w.deplink) + ((-1) * w.dep_acc) + (w.osd * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.deplink) + ((-1) * w.dep_acc) + (w.osd * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.deplink) + ((-1) * w.dep_acc) + ((-1) * w.maxlink) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.deplink) + ((-1) * w.dep_acc) + ((-1) * w.maxlink) + ((-1) * w.max_acc) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.deplink) + ((-1) * w.dep_acc) + ((-1) * w.max_acc) + (w.osd * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.float) + ((-1) * w.max_acc)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.float) + ((-1) * w.max_acc) + (w.nonfinal * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.float) + ((-1) * w.max_acc) + (w.osd * l) + (w.rightmost * l)) ∧
  0 < (((-1) * w.dep_acc) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.max_acc) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.dep_acc) + (w.osd * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.float) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.float) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.float) + (w.osd * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.float) + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.max_acc) + (w.osd * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < ((-1) * w.float * l) ∧
  0 < (w.max_acc + ((-1) * w.float * l)) ∧
  0 < (w.max_acc + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.max_acc + (w.osd * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.maxlink) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < ((-1) * w.max_acc) ∧
  0 < (((-1) * w.max_acc) + (w.nonfinal * l)) ∧
  0 < (((-1) * w.max_acc) + (w.osd * l) + (w.rightmost * l)) ∧
  0 < 0 ∧
  0 < (((-1) * w.dock_prev) + ((-1) * w.float) + ((-1) * w.max_acc) + (2 * w.deplink) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l) + (2 * w.clash * l)) ∧
  0 < (((-1) * w.dock_prev) + ((-1) * w.float) + ((-1) * w.max_acc) + (2 * w.deplink) + (w.rightmost * l) + ((-1) * w.float * l) + (2 * w.clash * l)) ∧
  0 < (((-1) * w.float) + ((-1) * w.max_acc) + (2 * w.deplink) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l) + (2 * w.clash * l)) ∧
  0 < (((-1) * w.float) + ((-1) * w.max_acc) + (2 * w.deplink) + (w.locality * l) + (w.rightmost * l) + ((-1) * w.float * l) + (2 * w.clash * l)) ∧
  0 < (((-1) * w.float) + ((-1) * w.max_acc) + (2 * w.deplink) + (w.rightmost * l) + ((-1) * w.float * l) + (2 * w.clash * l)) ∧
  0 < (w.deplink + ((-1) * w.dock_prev) + ((-1) * w.float) + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.nonfinal * l) + ((-1) * w.float * l) + (2 * w.clash * l)) ∧
  0 < (w.deplink + ((-1) * w.dock_prev) + ((-1) * w.float) + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.rightmost * l) + ((-1) * w.float * l) + (2 * w.clash * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.nonfinal * l) + ((-1) * w.float * l) + (2 * w.clash * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.rightmost * l) + ((-1) * w.float * l) + (2 * w.clash * l)) ∧
  0 < (((-1) * w.dock_prev) + ((-1) * w.float) + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.dock_prev) + ((-1) * w.float) + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.float) + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.float) + ((-1) * w.max_acc) + (2 * w.deplink) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + ((-1) * w.dock_prev) + ((-1) * w.float) + ((-1) * w.max_acc) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + ((-1) * w.float) + ((-1) * w.max_acc) + (w.clash * l) + (w.locality * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + ((-1) * w.float) + ((-1) * w.max_acc) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + ((-1) * w.float) + ((-1) * w.max_acc) + (w.clash * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.dock_prev) + ((-1) * w.float) + ((-1) * w.max_acc) + (w.clash * l)) ∧
  0 < (w.deplink + ((-1) * w.dock_prev) + ((-1) * w.float) + ((-1) * w.max_acc) + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-1) * w.dock_prev) + ((-1) * w.float) + (w.clash * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.dock_prev) + ((-1) * w.float) + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + ((-1) * w.max_acc) + (w.clash * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + ((-1) * w.max_acc) + (w.clash * l) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + ((-1) * w.max_acc) + (w.clash * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + (w.clash * l) + (w.locality * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.clash * l) + (w.locality * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.clash * l) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.clash * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + (w.clash * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + (w.clash * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + (w.clash * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.clash * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.dock_prev) + ((-1) * w.float) + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.dep_acc) + ((-1) * w.float) + ((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.maxlink) + (w.clash * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.maxlink) + (w.clash * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + ((-1) * w.float * l)) ∧
  0 < (((-1) * w.maxlink) + ((-1) * w.max_acc) + (w.clash * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + ((-1) * w.dock_prev) + ((-1) * w.float) + ((-1) * w.max_acc) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + ((-1) * w.float) + ((-1) * w.max_acc) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + ((-1) * w.float) + ((-1) * w.max_acc) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + ((-1) * w.float) + ((-1) * w.max_acc) + (w.locality * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.dep_acc) + ((-1) * w.float) + ((-1) * w.max_acc) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.dock_prev) + ((-1) * w.float) + ((-1) * w.max_acc) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.dock_prev) + ((-1) * w.float) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + ((-1) * w.max_acc) + (w.nonfinal * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + ((-1) * w.max_acc) + (w.nonfinal * l) + (w.rightmost * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + ((-1) * w.max_acc) + (w.rightmost * l)) ∧
  0 < (w.deplink + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.locality * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.locality * l) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.locality * l) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.locality * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + (w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.float) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.nonfinal * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.deplink + ((-1) * w.max_acc) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < (w.nonfinal * l) ∧
  0 < ((w.nonfinal * l) + ((-1) * w.float * l)) ∧
  0 < ((w.osd * l) + (w.rightmost * l) + ((-1) * w.float * l)) ∧
  0 < ((w.osd * l) + (w.rightmost * l))
def spring_loc (w : Weights) (l : ℝ) : Prop :=
  spring_loc_0 w l ∨ spring_loc_1 w l ∨ spring_loc_2 w l ∨ spring_loc_3 w l ∨ spring_loc_4 w l ∨ spring_loc_5 w l ∨ spring_loc_6 w l ∨ spring_loc_7 w l
def epenthesis (w : Weights) (l : ℝ) : Prop :=
  0 < (w.dep + w.deplink + w.maxlink + ((-1) * w.nocoda)) ∧
  0 < (w.dep + ((-1) * w.nocoda) + (w.rightmost * l) + (w.sync * l)) ∧
  0 < w.dep ∧
  0 < ((w.rightmost * l) + (w.sync * l)) ∧
  0 < (w.dock_prev + w.float + w.nocoda + w.osd + ((-1) * w.dep) + ((-1) * w.deplink)) ∧
  0 < (w.nocoda + ((-1) * w.dep)) ∧
  0 < (w.dock_prev + w.nocoda + ((-1) * w.dep) + (w.nonfinal * l))
def finiteRegion (w : Weights) (l : ℝ) : Prop :=
  bigfish w l ∧ bull_pl w l ∧ bull_sg w l ∧ chief_pl w l ∧ chief_sg w l ∧ fut_walk w l ∧ owl_2 w l ∧ owl_3 w l ∧ owl_sg w l ∧ spring_loc w l ∧ epenthesis w l
noncomputable def witness (l : ℝ) : Weights where
  clash := (4 + (2 * (1 / l)))
  dep := 1
  deplink := 1
  dep_acc := 0
  dock_prev := 3
  float := 0
  locality := 0
  maxlink := 1
  max_acc := 0
  nocoda := 2
  nonfinal := (1 / l)
  osd := (2 + (2 * (1 / l)))
  rightmost := (2 * (1 / l))
  sync := 0
theorem witness_nonnegative (l : ℝ) (hl : 0 < l) : nonnegative (witness l) := by
  dsimp [nonnegative, witness]
  refine ⟨by positivity, by positivity, by positivity, by positivity, by positivity, by positivity, by positivity, by positivity, by positivity, by positivity, by positivity, by positivity, by positivity, by positivity⟩
theorem epenthesis_witness (l : ℝ) (hl : 0 < l) : epenthesis (witness l) l := by
  have hn : l ≠ 0 := ne_of_gt hl
  unfold epenthesis
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hp : 0 < l / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < l / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < l / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (5 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < l / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (5 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
theorem bigfish_0_witness (l : ℝ) (hl : 0 < l) : bigfish_0 (witness l) l := by
  have hn : l ≠ 0 := ne_of_gt hl
  unfold bigfish_0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hp : 0 < l / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((2 * (l ^ 2)) + (4 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < l / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (l + (2 * (l ^ 2))) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (l + (2 * (l ^ 2))) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (l + (2 * (l ^ 2))) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < l / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((2 * (l ^ 2)) + (4 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < l / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((2 * (l ^ 2)) + (4 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < l / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < l / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((2 * (l ^ 2)) + (4 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < l / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((2 * (l ^ 2)) + (4 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < l / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((2 * (l ^ 2)) + (4 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < l / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (4 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (5 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (6 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (6 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (5 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (6 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (5 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (6 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (6 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (4 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (3 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (4 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (2 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (2 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (4 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (4 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (4 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (4 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (3 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (4 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * (l ^ 2)) + (7 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * (l ^ 2)) + (7 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * (l ^ 2)) + (7 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (4 * (l ^ 2)) + (9 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (4 * (l ^ 2)) + (11 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (4 * (l ^ 2)) + (10 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (4 * (l ^ 2)) + (9 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (4 * (l ^ 2)) + (11 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (4 * (l ^ 2)) + (10 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (4 * (l ^ 2)) + (11 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (4 * (l ^ 2)) + (9 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (4 * (l ^ 2)) + (7 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (4 * (l ^ 2)) + (9 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (4 * (l ^ 2)) + (8 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (4 * (l ^ 2)) + (9 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (4 * (l ^ 2)) + (7 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (4 * (l ^ 2)) + (9 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (4 * (l ^ 2)) + (8 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (4 * (l ^ 2)) + (9 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (4 * (l ^ 2)) + (9 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (4 * (l ^ 2)) + (9 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (4 * (l ^ 2)) + (5 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (4 * (l ^ 2)) + (6 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (4 * (l ^ 2)) + (7 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (4 * (l ^ 2)) + (7 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (4 * (l ^ 2)) + (7 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * l) + (4 * (l ^ 2))) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * (l ^ 2)) + (5 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * l) + (4 * (l ^ 2))) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * (l ^ 2)) + (5 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * l) + (4 * (l ^ 2))) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * l) + (4 * (l ^ 2))) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * l) + (4 * (l ^ 2))) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((2 * l) + (4 * (l ^ 2))) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((2 * l) + (4 * (l ^ 2))) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((2 * l) + (4 * (l ^ 2))) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (4 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (3 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (4 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (3 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (4 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (3 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (4 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (4 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (3 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (4 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (3 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < l / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((2 * (l ^ 2)) + (4 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
theorem bull_pl_2_witness (l : ℝ) (hl : 0 < l) : bull_pl_2 (witness l) l := by
  have hn : l ≠ 0 := ne_of_gt hl
  unfold bull_pl_2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hp : 0 < (4 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (6 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (6 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (5 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * (l ^ 2)) + (6 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * (l ^ 2)) + (5 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * (l ^ 2)) + (6 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * (l ^ 2)) + (7 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((3 * l) + (4 * (l ^ 2))) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * (l ^ 2)) + (5 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (3 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((2 * (l ^ 2)) + (6 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (3 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((2 * (l ^ 2)) + (6 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (3 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((2 * (l ^ 2)) + (6 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((2 * (l ^ 2)) + (3 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((2 * (l ^ 2)) + (3 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
theorem bull_sg_0_witness (l : ℝ) (hl : 0 < l) : bull_sg_0 (witness l) l := by
  have hn : l ≠ 0 := ne_of_gt hl
  unfold bull_sg_0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hp : 0 < (l + (2 * (l ^ 2))) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (l + (2 * (l ^ 2))) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < l / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * l) + (4 * (l ^ 2))) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * (l ^ 2)) + (5 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((2 * l) + (4 * (l ^ 2))) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((3 * l) + (4 * (l ^ 2))) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (4 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < l / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < l / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
theorem chief_pl_0_witness (l : ℝ) (hl : 0 < l) : chief_pl_0 (witness l) l := by
  have hn : l ≠ 0 := ne_of_gt hl
  unfold chief_pl_0
  refine ⟨?_, ?_, ?_⟩
  · have hp : 0 < (2 + l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < l / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
theorem chief_sg_0_witness (l : ℝ) (hl : 0 < l) : chief_sg_0 (witness l) l := by
  have hn : l ≠ 0 := ne_of_gt hl
  unfold chief_sg_0
  refine ⟨?_, ?_⟩
  · have hp : 0 < (2 + l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < l / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
theorem fut_walk_5_witness (l : ℝ) (hl : 0 < l) : fut_walk_5 (witness l) l := by
  have hn : l ≠ 0 := ne_of_gt hl
  unfold fut_walk_5
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hp : 0 < ((2 * (l ^ 2)) + (3 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((7 * l) + (8 * (l ^ 2))) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((8 * (l ^ 2)) + (9 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (4 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (4 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (4 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (4 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (4 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (7 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (8 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (7 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (8 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (7 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (8 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (7 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (7 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (8 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (7 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (7 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (8 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (9 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (9 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (5 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (2 * (l ^ 2)) + (8 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (2 * (l ^ 2)) + (8 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (6 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (2 * (l ^ 2)) + (8 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (5 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (6 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (5 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (2 * (l ^ 2)) + (8 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (5 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (2 * (l ^ 2)) + (8 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (6 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (2 * (l ^ 2)) + (6 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (2 * (l ^ 2)) + (6 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (3 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * (l ^ 2)) + (5 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * (l ^ 2)) + (6 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * (l ^ 2)) + (5 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * (l ^ 2)) + (6 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * (l ^ 2)) + (5 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * (l ^ 2)) + (6 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * (l ^ 2)) + (5 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * (l ^ 2)) + (6 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * (l ^ 2)) + (5 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * (l ^ 2)) + (6 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (4 * (l ^ 2)) + (8 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (4 * (l ^ 2)) + (8 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (4 * (l ^ 2)) + (9 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (4 * (l ^ 2)) + (10 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (4 * (l ^ 2)) + (11 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (4 * (l ^ 2)) + (10 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (4 * (l ^ 2)) + (11 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (4 * (l ^ 2)) + (6 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((3 * l) + (4 * (l ^ 2))) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((3 * l) + (4 * (l ^ 2))) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((3 * l) + (4 * (l ^ 2))) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (3 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (3 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (3 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (3 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (3 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (3 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (3 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((2 * (l ^ 2)) + (3 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((2 * (l ^ 2)) + (3 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
theorem owl_2_2_witness (l : ℝ) (hl : 0 < l) : owl_2_2 (witness l) l := by
  have hn : l ≠ 0 := ne_of_gt hl
  unfold owl_2_2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hp : 0 < (4 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (6 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (5 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (5 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * (l ^ 2)) + (6 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * (l ^ 2)) + (7 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * (l ^ 2)) + (5 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * (l ^ 2)) + (6 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((3 * l) + (4 * (l ^ 2))) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * (l ^ 2)) + (5 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (3 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((2 * (l ^ 2)) + (6 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (3 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((2 * (l ^ 2)) + (6 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (3 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((2 * (l ^ 2)) + (6 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((2 * (l ^ 2)) + (3 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((2 * (l ^ 2)) + (3 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
theorem owl_3_1_witness (l : ℝ) (hl : 0 < l) : owl_3_1 (witness l) l := by
  have hn : l ≠ 0 := ne_of_gt hl
  unfold owl_3_1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hp : 0 < (2 + (2 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (2 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < l / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (5 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (3 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * (l ^ 2)) + (5 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (4 * (l ^ 2)) + (8 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * (l ^ 2)) + (6 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * (l ^ 2)) + (6 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (4 * (l ^ 2)) + (6 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (6 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (3 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (5 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (4 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (6 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (5 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < l / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (3 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (5 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (3 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < l / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (3 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (2 + (5 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (3 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < l / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * l) + (4 * (l ^ 2))) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
theorem owl_sg_0_witness (l : ℝ) (hl : 0 < l) : owl_sg_0 (witness l) l := by
  have hn : l ≠ 0 := ne_of_gt hl
  unfold owl_sg_0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hp : 0 < (l + (2 * (l ^ 2))) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (l + (2 * (l ^ 2))) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < l / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * l) + (4 * (l ^ 2))) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((2 * l) + (4 * (l ^ 2))) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < l / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < l / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
theorem spring_loc_0_witness (l : ℝ) (hl : 0 < l) : spring_loc_0 (witness l) l := by
  have hn : l ≠ 0 := ne_of_gt hl
  unfold spring_loc_0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hp : 0 < ((2 * (l ^ 2)) + (4 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((2 * (l ^ 2)) + (4 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < l / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < l / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((2 * (l ^ 2)) + (4 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((2 * (l ^ 2)) + (4 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((8 * (l ^ 2)) + (10 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((8 * (l ^ 2)) + (11 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((8 * (l ^ 2)) + (11 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((7 * l) + (8 * (l ^ 2))) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((8 * l) + (8 * (l ^ 2))) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((8 * l) + (8 * (l ^ 2))) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((8 * (l ^ 2)) + (9 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((5 * l) + (8 * (l ^ 2))) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((6 * l) + (8 * (l ^ 2))) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * (l ^ 2)) + (10 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * (l ^ 2)) + (10 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * (l ^ 2)) + (7 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * (l ^ 2)) + (7 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((3 * l) + (4 * (l ^ 2))) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * (l ^ 2)) + (6 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * (l ^ 2)) + (6 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * (l ^ 2)) + (7 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * (l ^ 2)) + (6 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * (l ^ 2)) + (7 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * (l ^ 2)) + (8 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * (l ^ 2)) + (8 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * (l ^ 2)) + (6 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * (l ^ 2)) + (7 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * (l ^ 2)) + (8 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * (l ^ 2)) + (7 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * (l ^ 2)) + (8 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * (l ^ 2)) + (8 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((3 * l) + (4 * (l ^ 2))) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * l) + (4 * (l ^ 2))) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * l) + (4 * (l ^ 2))) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * (l ^ 2)) + (6 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * (l ^ 2)) + (7 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * (l ^ 2)) + (8 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * l) + (4 * (l ^ 2))) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * l) + (4 * (l ^ 2))) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * (l ^ 2)) + (6 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * l) + (4 * (l ^ 2))) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * (l ^ 2)) + (6 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((4 * (l ^ 2)) + (6 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (l + (4 * (l ^ 2))) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (5 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (7 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (6 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (5 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (7 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (6 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (7 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (6 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (7 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (6 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (5 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (7 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (6 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (5 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (7 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (6 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (3 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (3 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (5 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (7 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (6 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (7 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (3 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (3 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (3 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (4 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((2 * (l ^ 2)) + (7 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (4 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((2 * (l ^ 2)) + (7 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (3 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (3 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (3 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (4 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((2 * (l ^ 2)) + (7 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (3 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (4 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((2 * (l ^ 2)) + (7 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (3 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (4 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (4 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((2 * (l ^ 2)) + (7 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((2 * (l ^ 2)) + (7 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (3 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (4 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((2 * (l ^ 2)) + (7 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (4 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < ((2 * (l ^ 2)) + (7 * l)) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
  · have hp : 0 < (3 * l) / l := div_pos (by positivity) hl
    convert hp using 1 <;> dsimp [witness] <;> field_simp <;> ring
theorem witness_mem (l : ℝ) (hl : 0 < l) : finiteRegion (witness l) l := by
  unfold finiteRegion
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold bigfish
    left
    exact bigfish_0_witness l hl
  · unfold bull_pl
    right
    right
    exact bull_pl_2_witness l hl
  · unfold bull_sg
    left
    exact bull_sg_0_witness l hl
  · unfold chief_pl
    exact chief_pl_0_witness l hl
  · unfold chief_sg
    exact chief_sg_0_witness l hl
  · unfold fut_walk
    right
    right
    right
    right
    right
    left
    exact fut_walk_5_witness l hl
  · unfold owl_2
    right
    right
    exact owl_2_2_witness l hl
  · unfold owl_3
    right
    exact owl_3_1_witness l hl
  · unfold owl_sg
    left
    exact owl_sg_0_witness l hl
  · unfold spring_loc
    left
    exact spring_loc_0_witness l hl
  · exact epenthesis_witness l hl
theorem owl_zero_impossible (w : Weights) : ¬ owl_3 w 0 := by
  simp [owl_3, owl_3_0, owl_3_1]
theorem exact_projection (l : ℝ) :
    (∃ w : Weights, 0 ≤ l ∧ nonnegative w ∧ finiteRegion w l) ↔ 0 < l := by
  constructor
  · rintro ⟨w, hl, hw, hr⟩
    apply lt_of_le_of_ne hl
    intro hz
    subst l
    exact owl_zero_impossible w hr.2.2.2.2.2.2.2.1
  · intro hl
    exact ⟨witness l, le_of_lt hl, witness_nonnegative l hl, witness_mem l hl⟩
theorem exclusive_minima_iff {α : Type*} (candidates : Finset α)
    (score : α → ℝ) (correct : α → Prop) (hn : candidates.Nonempty) :
    (∃ a ∈ candidates, correct a ∧
      ∀ b ∈ candidates, ¬ correct b → score a < score b) ↔
    (∀ a ∈ candidates, (∀ b ∈ candidates, score a ≤ score b) → correct a) := by
  constructor
  · rintro ⟨a, ha, _, hab⟩ b hb hmin
    by_contra hbad
    exact (not_lt_of_ge (hmin a ha)) (hab b hb hbad)
  · intro h
    obtain ⟨a, ha, hmin⟩ := candidates.exists_min_image score hn
    refine ⟨a, ha, h a ha hmin, ?_⟩
    intro b hb hbad
    apply lt_of_le_of_ne (hmin b hb)
    intro heq
    apply hbad
    apply h b hb
    intro d hd
    rw [← heq]
    exact hmin d hd
end AccentRegion
