import PhonologicalOpacity.Attenuation.Productive.Baseline.CertificateParts.G37c_7_020
namespace ProductiveGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_1685 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","u","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1686 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","u","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1687 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","u","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1660 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_1661
  · exact partG37c_7_1662
  · exact partG37c_7_1663
  · exact partG37c_7_1664
  · exact partG37c_7_1665
  · exact partG37c_7_1666
  · exact partG37c_7_1667
  · exact partG37c_7_1682
  · exact partG37c_7_1683
  · exact partG37c_7_1684
  · exact partG37c_7_1685
  · exact partG37c_7_1686
  · exact partG37c_7_1687
theorem partG37c_7_1689 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","j","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1690 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","j","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1691 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","j","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1692 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","j","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1693 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","j","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1694 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","j","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1697 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","j","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1698 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","j","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1699 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","j","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1700 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","j","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1701 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","j","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1702 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","j","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1703 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","j","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1704 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","j","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1705 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","j","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1706 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","j","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1707 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","j","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1708 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","j","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1709 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","j","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1696 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","j","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_1697
  · exact partG37c_7_1698
  · exact partG37c_7_1699
  · exact partG37c_7_1700
  · exact partG37c_7_1701
  · exact partG37c_7_1702
  · exact partG37c_7_1703
  · exact partG37c_7_1704
  · exact partG37c_7_1705
  · exact partG37c_7_1706
  · exact partG37c_7_1707
  · exact partG37c_7_1708
  · exact partG37c_7_1709
theorem partG37c_7_1695 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","j","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_1696
theorem partG37c_7_1710 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","j","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1711 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","j","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1712 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","j","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1713 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","j","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1714 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","j","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1715 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","j","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1688 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_1689
  · exact partG37c_7_1690
  · exact partG37c_7_1691
  · exact partG37c_7_1692
  · exact partG37c_7_1693
  · exact partG37c_7_1694
  · exact partG37c_7_1695
  · exact partG37c_7_1710
  · exact partG37c_7_1711
  · exact partG37c_7_1712
  · exact partG37c_7_1713
  · exact partG37c_7_1714
  · exact partG37c_7_1715
theorem partG37c_7_1717 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","w","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1718 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","w","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1719 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","w","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1720 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","w","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1721 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","w","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1722 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","w","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1725 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","w","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1726 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","w","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1727 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","w","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1728 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","w","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1729 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","w","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1730 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","w","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1731 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","w","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1732 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","w","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1733 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","w","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1734 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","w","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1735 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","w","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1736 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","w","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1737 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","w","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1724 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","w","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_1725
  · exact partG37c_7_1726
  · exact partG37c_7_1727
  · exact partG37c_7_1728
  · exact partG37c_7_1729
  · exact partG37c_7_1730
  · exact partG37c_7_1731
  · exact partG37c_7_1732
  · exact partG37c_7_1733
  · exact partG37c_7_1734
  · exact partG37c_7_1735
  · exact partG37c_7_1736
  · exact partG37c_7_1737
theorem partG37c_7_1723 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","w","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_1724
theorem partG37c_7_1738 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","w","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1739 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","w","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1740 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","w","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1741 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","w","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1742 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","w","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1743 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","w","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1716 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_1717
  · exact partG37c_7_1718
  · exact partG37c_7_1719
  · exact partG37c_7_1720
  · exact partG37c_7_1721
  · exact partG37c_7_1722
  · exact partG37c_7_1723
  · exact partG37c_7_1738
  · exact partG37c_7_1739
  · exact partG37c_7_1740
  · exact partG37c_7_1741
  · exact partG37c_7_1742
  · exact partG37c_7_1743
theorem partG37c_7_1239 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_1240
  · exact partG37c_7_1268
  · exact partG37c_7_1324
  · exact partG37c_7_1352
  · exact partG37c_7_1408
  · exact partG37c_7_1436
  · exact partG37c_7_1492
  · exact partG37c_7_1520
  · exact partG37c_7_1576
  · exact partG37c_7_1604
  · exact partG37c_7_1660
  · exact partG37c_7_1688
  · exact partG37c_7_1716
theorem partG37c_7_1238 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="s" := by simpa using hx
  subst x
  exact partG37c_7_1239
theorem partG37c_7_1749 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1750 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1751 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1752 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1753 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1754 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1755 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1756 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1757 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1758 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1759 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1760 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1761 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1748 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_1749
  · exact partG37c_7_1750
  · exact partG37c_7_1751
  · exact partG37c_7_1752
  · exact partG37c_7_1753
  · exact partG37c_7_1754
  · exact partG37c_7_1755
  · exact partG37c_7_1756
  · exact partG37c_7_1757
  · exact partG37c_7_1758
  · exact partG37c_7_1759
  · exact partG37c_7_1760
  · exact partG37c_7_1761
theorem partG37c_7_1747 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_1748
theorem partG37c_7_1762 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1763 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1764 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveGua
