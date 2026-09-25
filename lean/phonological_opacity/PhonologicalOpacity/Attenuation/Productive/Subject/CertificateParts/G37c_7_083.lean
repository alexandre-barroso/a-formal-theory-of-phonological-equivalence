import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.G37c_7_082
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_6647 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","j","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6648 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","j","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6649 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","j","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6650 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","j","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6651 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","j","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6652 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","j","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6653 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","j","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6640 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","j","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_6641
  · exact partG37c_7_6642
  · exact partG37c_7_6643
  · exact partG37c_7_6644
  · exact partG37c_7_6645
  · exact partG37c_7_6646
  · exact partG37c_7_6647
  · exact partG37c_7_6648
  · exact partG37c_7_6649
  · exact partG37c_7_6650
  · exact partG37c_7_6651
  · exact partG37c_7_6652
  · exact partG37c_7_6653
theorem partG37c_7_6639 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","j","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_6640
theorem partG37c_7_6654 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","j","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6655 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","j","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6656 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","j","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6657 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","j","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6658 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","j","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6659 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","j","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6632 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_6633
  · exact partG37c_7_6634
  · exact partG37c_7_6635
  · exact partG37c_7_6636
  · exact partG37c_7_6637
  · exact partG37c_7_6638
  · exact partG37c_7_6639
  · exact partG37c_7_6654
  · exact partG37c_7_6655
  · exact partG37c_7_6656
  · exact partG37c_7_6657
  · exact partG37c_7_6658
  · exact partG37c_7_6659
theorem partG37c_7_6661 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","w","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6662 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","w","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6663 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","w","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6664 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","w","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6665 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","w","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6666 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","w","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6669 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","w","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6670 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","w","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6671 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","w","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6672 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","w","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6673 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","w","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6674 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","w","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6675 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","w","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6676 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","w","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6677 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","w","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6678 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","w","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6679 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","w","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6680 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","w","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6681 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","w","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6668 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","w","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_6669
  · exact partG37c_7_6670
  · exact partG37c_7_6671
  · exact partG37c_7_6672
  · exact partG37c_7_6673
  · exact partG37c_7_6674
  · exact partG37c_7_6675
  · exact partG37c_7_6676
  · exact partG37c_7_6677
  · exact partG37c_7_6678
  · exact partG37c_7_6679
  · exact partG37c_7_6680
  · exact partG37c_7_6681
theorem partG37c_7_6667 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","w","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_6668
theorem partG37c_7_6682 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","w","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6683 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","w","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6684 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","w","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6685 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","w","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6686 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","w","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6687 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","w","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6660 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_6661
  · exact partG37c_7_6662
  · exact partG37c_7_6663
  · exact partG37c_7_6664
  · exact partG37c_7_6665
  · exact partG37c_7_6666
  · exact partG37c_7_6667
  · exact partG37c_7_6682
  · exact partG37c_7_6683
  · exact partG37c_7_6684
  · exact partG37c_7_6685
  · exact partG37c_7_6686
  · exact partG37c_7_6687
theorem partG37c_7_6183 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_6184
  · exact partG37c_7_6212
  · exact partG37c_7_6268
  · exact partG37c_7_6296
  · exact partG37c_7_6352
  · exact partG37c_7_6380
  · exact partG37c_7_6436
  · exact partG37c_7_6464
  · exact partG37c_7_6520
  · exact partG37c_7_6548
  · exact partG37c_7_6604
  · exact partG37c_7_6632
  · exact partG37c_7_6660
theorem partG37c_7_6182 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="s" := by simpa using hx
  subst x
  exact partG37c_7_6183
theorem partG37c_7_6691 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","∅","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6692 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","∅","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6693 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","∅","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6694 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","∅","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6695 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","∅","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6696 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","∅","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6699 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","∅","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6700 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","∅","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6701 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","∅","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6702 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","∅","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6703 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","∅","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6704 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","∅","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6705 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","∅","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6706 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","∅","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6707 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","∅","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6708 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","∅","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6709 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","∅","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6710 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","∅","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6711 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","∅","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6698 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","∅","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_6699
  · exact partG37c_7_6700
  · exact partG37c_7_6701
  · exact partG37c_7_6702
  · exact partG37c_7_6703
  · exact partG37c_7_6704
  · exact partG37c_7_6705
  · exact partG37c_7_6706
  · exact partG37c_7_6707
  · exact partG37c_7_6708
  · exact partG37c_7_6709
  · exact partG37c_7_6710
  · exact partG37c_7_6711
theorem partG37c_7_6697 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","∅","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_6698
theorem partG37c_7_6712 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","∅","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6713 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","∅","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6714 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","∅","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6715 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","∅","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6716 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","∅","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6717 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","∅","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6690 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_6691
  · exact partG37c_7_6692
  · exact partG37c_7_6693
  · exact partG37c_7_6694
  · exact partG37c_7_6695
  · exact partG37c_7_6696
  · exact partG37c_7_6697
  · exact partG37c_7_6712
  · exact partG37c_7_6713
  · exact partG37c_7_6714
  · exact partG37c_7_6715
  · exact partG37c_7_6716
  · exact partG37c_7_6717
theorem partG37c_7_6721 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6722 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6723 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6724 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6725 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6726 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveSubjectGua
