import PhonologicalOpacity.Attenuation.Productive.Baseline.ProductiveTheory
namespace ProductiveGua
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem partC24ei_4_1 : check uC24ei (2) (-2) outC24ei ["k","p","e","∅"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC24ei_4_2 : check uC24ei (2) (-2) outC24ei ["k","p","e","a"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC24ei_4_3 : check uC24ei (2) (-2) outC24ei ["k","p","e","ɜ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC24ei_4_4 : check uC24ei (2) (-2) outC24ei ["k","p","e","ɛ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC24ei_4_5 : check uC24ei (2) (-2) outC24ei ["k","p","e","e"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC24ei_4_6 : check uC24ei (2) (-2) outC24ei ["k","p","e","ɪ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC24ei_4_7 : check uC24ei (2) (-2) outC24ei ["k","p","e","i"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC24ei_4_8 : check uC24ei (2) (-2) outC24ei ["k","p","e","ɔ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC24ei_4_9 : check uC24ei (2) (-2) outC24ei ["k","p","e","o"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC24ei_4_10 : check uC24ei (2) (-2) outC24ei ["k","p","e","ʊ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC24ei_4_11 : check uC24ei (2) (-2) outC24ei ["k","p","e","u"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC24ei_4_12 : check uC24ei (2) (-2) outC24ei ["k","p","e","j"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC24ei_4_13 : check uC24ei (2) (-2) outC24ei ["k","p","e","w"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem checkedC24ei_4 : check uC24ei (2) (-2) outC24ei ["k","p","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partC24ei_4_1
  · exact partC24ei_4_2
  · exact partC24ei_4_3
  · exact partC24ei_4_4
  · exact partC24ei_4_5
  · exact partC24ei_4_6
  · exact partC24ei_4_7
  · exact partC24ei_4_8
  · exact partC24ei_4_9
  · exact partC24ei_4_10
  · exact partC24ei_4_11
  · exact partC24ei_4_12
  · exact partC24ei_4_13
end ProductiveGua
