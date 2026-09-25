import PhonologicalOpacity.Attenuation.Core
import PhonologicalOpacity.Attenuation.Blocks.G34a
import PhonologicalOpacity.Attenuation.Blocks.G34b
import PhonologicalOpacity.Attenuation.Blocks.N7
import PhonologicalOpacity.Attenuation.Blocks.G37c
import PhonologicalOpacity.Attenuation.Blocks.C24ei
import PhonologicalOpacity.Attenuation.Blocks.OR38
import PhonologicalOpacity.Attenuation.Blocks.C21b
import PhonologicalOpacity.Attenuation.Blocks.C23UE
namespace Attenuation
open Retained Deletion
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem scores_goal_G34a : scores g34a 774 = (3, 0) := by decide +kernel
theorem certificate_G34a : checkAll g34a 774 3 0 = true := by
  apply assemble (n := 13) (by decide)
  intro b hb
  interval_cases b
  · exact block_G34a_0
  · exact block_G34a_1
  · exact block_G34a_2
  · exact block_G34a_3
  · exact block_G34a_4
  · exact block_G34a_5
  · exact block_G34a_6
  · exact block_G34a_7
  · exact block_G34a_8
  · exact block_G34a_9
  · exact block_G34a_10
  · exact block_G34a_11
  · exact block_G34a_12
theorem interval_G34a (lam : ℚ) (h0 : 0 ≤ lam) (h4 : lam < 1/4) :
    ∀ i ∈ carrier g34a, i ≠ 774 → pressure g34a lam 774 < pressure g34a lam i :=
  unique_min_on_interval certificate_G34a scores_goal_G34a lam h0 h4
#print axioms interval_G34a
theorem all_lambda_G34a (lam : ℚ) (h0 : 0 ≤ lam) :
    ∀ i ∈ carrier g34a, i ≠ 774 → pressure g34a lam 774 < pressure g34a lam i :=
  unique_min_all_lambda certificate_G34a scores_goal_G34a lam h0
#print axioms all_lambda_G34a

theorem scores_goal_G34b : scores g34b 957 = (2, 4) := by decide +kernel
theorem certificate_G34b : checkAll g34b 957 2 4 = true := by
  apply assemble (n := 13) (by decide)
  intro b hb
  interval_cases b
  · exact block_G34b_0
  · exact block_G34b_1
  · exact block_G34b_2
  · exact block_G34b_3
  · exact block_G34b_4
  · exact block_G34b_5
  · exact block_G34b_6
  · exact block_G34b_7
  · exact block_G34b_8
  · exact block_G34b_9
  · exact block_G34b_10
  · exact block_G34b_11
  · exact block_G34b_12
theorem interval_G34b (lam : ℚ) (h0 : 0 ≤ lam) (h4 : lam < 1/4) :
    ∀ i ∈ carrier g34b, i ≠ 957 → pressure g34b lam 957 < pressure g34b lam i :=
  unique_min_on_interval certificate_G34b scores_goal_G34b lam h0 h4
#print axioms interval_G34b
theorem rival_mem_G34b : 1126 ∈ carrier g34b := by decide
theorem rival_ne_G34b : (1126 : Nat) ≠ 957 := by decide
theorem scores_rival_G34b : scores g34b 1126 = (3, 0) := by decide +kernel
theorem scores_G34b :
    oldScore g34b 1126 = oldScore g34b 957 + 1 ∧
    newScore g34b 957 = newScore g34b 1126 + 4 := by
  unfold oldScore newScore; rw [scores_goal_G34b, scores_rival_G34b]; constructor <;> rfl
theorem tie_G34b : pressure g34b (1/4) 1126 = pressure g34b (1/4) 957 :=
  tie_at_quarter scores_G34b
theorem rival_wins_G34b (lam : ℚ) (h : 1/4 < lam) :
    pressure g34b lam 1126 < pressure g34b lam 957 :=
  rival_wins_above_quarter scores_G34b lam h
#print axioms tie_G34b
#print axioms rival_wins_G34b

theorem scores_goal_N7 : scores n7 82 = (1, 0) := by decide +kernel
theorem certificate_N7 : checkAll n7 82 1 0 = true := by
  apply assemble (n := 1) (by decide)
  intro b hb
  interval_cases b
  · exact block_N7_0
theorem interval_N7 (lam : ℚ) (h0 : 0 ≤ lam) (h4 : lam < 1/4) :
    ∀ i ∈ carrier n7, i ≠ 82 → pressure n7 lam 82 < pressure n7 lam i :=
  unique_min_on_interval certificate_N7 scores_goal_N7 lam h0 h4
#print axioms interval_N7
theorem all_lambda_N7 (lam : ℚ) (h0 : 0 ≤ lam) :
    ∀ i ∈ carrier n7, i ≠ 82 → pressure n7 lam 82 < pressure n7 lam i :=
  unique_min_all_lambda certificate_N7 scores_goal_N7 lam h0
#print axioms all_lambda_N7

theorem scores_goal_G37c : scores g37 1584 = (3, 4) := by decide +kernel
theorem certificate_G37c : checkAll g37 1584 3 4 = true := by
  apply assemble (n := 13) (by decide)
  intro b hb
  interval_cases b
  · exact block_G37c_0
  · exact block_G37c_1
  · exact block_G37c_2
  · exact block_G37c_3
  · exact block_G37c_4
  · exact block_G37c_5
  · exact block_G37c_6
  · exact block_G37c_7
  · exact block_G37c_8
  · exact block_G37c_9
  · exact block_G37c_10
  · exact block_G37c_11
  · exact block_G37c_12
theorem interval_G37c (lam : ℚ) (h0 : 0 ≤ lam) (h4 : lam < 1/4) :
    ∀ i ∈ carrier g37, i ≠ 1584 → pressure g37 lam 1584 < pressure g37 lam i :=
  unique_min_on_interval certificate_G37c scores_goal_G37c lam h0 h4
#print axioms interval_G37c
theorem rival_mem_G37c : 1753 ∈ carrier g37 := by decide
theorem rival_ne_G37c : (1753 : Nat) ≠ 1584 := by decide
theorem scores_rival_G37c : scores g37 1753 = (4, 0) := by decide +kernel
theorem scores_G37c :
    oldScore g37 1753 = oldScore g37 1584 + 1 ∧
    newScore g37 1584 = newScore g37 1753 + 4 := by
  unfold oldScore newScore; rw [scores_goal_G37c, scores_rival_G37c]; constructor <;> rfl
theorem tie_G37c : pressure g37 (1/4) 1753 = pressure g37 (1/4) 1584 :=
  tie_at_quarter scores_G37c
theorem rival_wins_G37c (lam : ℚ) (h : 1/4 < lam) :
    pressure g37 lam 1753 < pressure g37 lam 1584 :=
  rival_wins_above_quarter scores_G37c lam h
#print axioms tie_G37c
#print axioms rival_wins_G37c

theorem scores_goal_C24ei : scores c24 63 = (2, 0) := by decide +kernel
theorem certificate_C24ei : checkAll c24 63 2 0 = true := by
  apply assemble (n := 1) (by decide)
  intro b hb
  interval_cases b
  · exact block_C24ei_0
theorem interval_C24ei (lam : ℚ) (h0 : 0 ≤ lam) (h4 : lam < 1/4) :
    ∀ i ∈ carrier c24, i ≠ 63 → pressure c24 lam 63 < pressure c24 lam i :=
  unique_min_on_interval certificate_C24ei scores_goal_C24ei lam h0 h4
#print axioms interval_C24ei
theorem all_lambda_C24ei (lam : ℚ) (h0 : 0 ≤ lam) :
    ∀ i ∈ carrier c24, i ≠ 63 → pressure c24 lam 63 < pressure c24 lam i :=
  unique_min_all_lambda certificate_C24ei scores_goal_C24ei lam h0
#print axioms all_lambda_C24ei

theorem scores_goal_OR38 : scores or38 1261 = (21, 4) := by decide +kernel
theorem certificate_OR38 : checkAll or38 1261 21 4 = true := by
  apply assemble (n := 13) (by decide)
  intro b hb
  interval_cases b
  · exact block_OR38_0
  · exact block_OR38_1
  · exact block_OR38_2
  · exact block_OR38_3
  · exact block_OR38_4
  · exact block_OR38_5
  · exact block_OR38_6
  · exact block_OR38_7
  · exact block_OR38_8
  · exact block_OR38_9
  · exact block_OR38_10
  · exact block_OR38_11
  · exact block_OR38_12
theorem interval_OR38 (lam : ℚ) (h0 : 0 ≤ lam) (h4 : lam < 1/4) :
    ∀ i ∈ carrier or38, i ≠ 1261 → pressure or38 lam 1261 < pressure or38 lam i :=
  unique_min_on_interval certificate_OR38 scores_goal_OR38 lam h0 h4
#print axioms interval_OR38
theorem rival_mem_OR38 : 1430 ∈ carrier or38 := by decide
theorem rival_ne_OR38 : (1430 : Nat) ≠ 1261 := by decide
theorem scores_rival_OR38 : scores or38 1430 = (22, 0) := by decide +kernel
theorem scores_OR38 :
    oldScore or38 1430 = oldScore or38 1261 + 1 ∧
    newScore or38 1261 = newScore or38 1430 + 4 := by
  unfold oldScore newScore; rw [scores_goal_OR38, scores_rival_OR38]; constructor <;> rfl
theorem tie_OR38 : pressure or38 (1/4) 1430 = pressure or38 (1/4) 1261 :=
  tie_at_quarter scores_OR38
theorem rival_wins_OR38 (lam : ℚ) (h : 1/4 < lam) :
    pressure or38 lam 1430 < pressure or38 lam 1261 :=
  rival_wins_above_quarter scores_OR38 lam h
#print axioms tie_OR38
#print axioms rival_wins_OR38

theorem scores_goal_C21b : scores c21 117 = (20, 0) := by decide +kernel
theorem certificate_C21b : checkAll c21 117 20 0 = true := by
  apply assemble (n := 1) (by decide)
  intro b hb
  interval_cases b
  · exact block_C21b_0
theorem interval_C21b (lam : ℚ) (h0 : 0 ≤ lam) (h4 : lam < 1/4) :
    ∀ i ∈ carrier c21, i ≠ 117 → pressure c21 lam 117 < pressure c21 lam i :=
  unique_min_on_interval certificate_C21b scores_goal_C21b lam h0 h4
#print axioms interval_C21b
theorem all_lambda_C21b (lam : ℚ) (h0 : 0 ≤ lam) :
    ∀ i ∈ carrier c21, i ≠ 117 → pressure c21 lam 117 < pressure c21 lam i :=
  unique_min_all_lambda certificate_C21b scores_goal_C21b lam h0
#print axioms all_lambda_C21b

theorem scores_goal_C23UE : scores c23 159 = (2, 0) := by decide +kernel
theorem certificate_C23UE : checkAll c23 159 2 0 = true := by
  apply assemble (n := 1) (by decide)
  intro b hb
  interval_cases b
  · exact block_C23UE_0
theorem interval_C23UE (lam : ℚ) (h0 : 0 ≤ lam) (h4 : lam < 1/4) :
    ∀ i ∈ carrier c23, i ≠ 159 → pressure c23 lam 159 < pressure c23 lam i :=
  unique_min_on_interval certificate_C23UE scores_goal_C23UE lam h0 h4
#print axioms interval_C23UE
theorem all_lambda_C23UE (lam : ℚ) (h0 : 0 ≤ lam) :
    ∀ i ∈ carrier c23, i ≠ 159 → pressure c23 lam 159 < pressure c23 lam i :=
  unique_min_all_lambda certificate_C23UE scores_goal_C23UE lam h0
#print axioms all_lambda_C23UE

end Attenuation
