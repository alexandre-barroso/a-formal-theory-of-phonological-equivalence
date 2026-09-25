import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.G37c_7_069
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_5605 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɜ","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5608 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɜ","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5609 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɜ","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5610 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɜ","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5611 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɜ","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5612 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɜ","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5613 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɜ","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5614 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɜ","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5615 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɜ","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5616 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɜ","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5617 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɜ","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5618 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɜ","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5619 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɜ","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5620 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɜ","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5607 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɜ","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_5608
  · exact partG37c_7_5609
  · exact partG37c_7_5610
  · exact partG37c_7_5611
  · exact partG37c_7_5612
  · exact partG37c_7_5613
  · exact partG37c_7_5614
  · exact partG37c_7_5615
  · exact partG37c_7_5616
  · exact partG37c_7_5617
  · exact partG37c_7_5618
  · exact partG37c_7_5619
  · exact partG37c_7_5620
theorem partG37c_7_5606 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɜ","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_5607
theorem partG37c_7_5621 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɜ","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5566 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_5567
  · exact partG37c_7_5582
  · exact partG37c_7_5583
  · exact partG37c_7_5584
  · exact partG37c_7_5585
  · exact partG37c_7_5586
  · exact partG37c_7_5587
  · exact partG37c_7_5602
  · exact partG37c_7_5603
  · exact partG37c_7_5604
  · exact partG37c_7_5605
  · exact partG37c_7_5606
  · exact partG37c_7_5621
theorem partG37c_7_5625 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5626 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5627 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5628 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5629 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5630 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5631 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5632 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5633 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5634 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5635 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5636 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5637 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5624 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_5625
  · exact partG37c_7_5626
  · exact partG37c_7_5627
  · exact partG37c_7_5628
  · exact partG37c_7_5629
  · exact partG37c_7_5630
  · exact partG37c_7_5631
  · exact partG37c_7_5632
  · exact partG37c_7_5633
  · exact partG37c_7_5634
  · exact partG37c_7_5635
  · exact partG37c_7_5636
  · exact partG37c_7_5637
theorem partG37c_7_5623 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_5624
theorem partG37c_7_5638 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5639 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5640 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5641 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5642 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5645 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5646 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5647 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5648 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5649 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5650 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5651 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5652 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5653 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5654 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5655 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5656 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5657 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5644 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_5645
  · exact partG37c_7_5646
  · exact partG37c_7_5647
  · exact partG37c_7_5648
  · exact partG37c_7_5649
  · exact partG37c_7_5650
  · exact partG37c_7_5651
  · exact partG37c_7_5652
  · exact partG37c_7_5653
  · exact partG37c_7_5654
  · exact partG37c_7_5655
  · exact partG37c_7_5656
  · exact partG37c_7_5657
theorem partG37c_7_5643 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_5644
theorem partG37c_7_5658 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5659 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5660 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5661 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5664 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5665 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5666 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5667 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5668 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5669 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5670 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5671 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5672 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5673 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5674 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5675 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5676 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5663 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_5664
  · exact partG37c_7_5665
  · exact partG37c_7_5666
  · exact partG37c_7_5667
  · exact partG37c_7_5668
  · exact partG37c_7_5669
  · exact partG37c_7_5670
  · exact partG37c_7_5671
  · exact partG37c_7_5672
  · exact partG37c_7_5673
  · exact partG37c_7_5674
  · exact partG37c_7_5675
  · exact partG37c_7_5676
theorem partG37c_7_5662 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_5663
theorem partG37c_7_5677 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5622 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_5623
  · exact partG37c_7_5638
  · exact partG37c_7_5639
  · exact partG37c_7_5640
  · exact partG37c_7_5641
  · exact partG37c_7_5642
  · exact partG37c_7_5643
  · exact partG37c_7_5658
  · exact partG37c_7_5659
  · exact partG37c_7_5660
  · exact partG37c_7_5661
  · exact partG37c_7_5662
  · exact partG37c_7_5677
theorem partG37c_7_5681 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5682 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5683 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5684 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5685 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5686 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveSubjectGua
