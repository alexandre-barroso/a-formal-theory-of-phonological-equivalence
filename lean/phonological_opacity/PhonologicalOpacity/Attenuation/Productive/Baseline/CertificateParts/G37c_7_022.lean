import PhonologicalOpacity.Attenuation.Productive.Baseline.CertificateParts.G37c_7_021
namespace ProductiveGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_1765 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1766 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1769 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1770 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1771 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1772 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1773 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1774 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1775 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1776 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1777 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1778 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1779 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1780 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1781 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1768 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_1769
  · exact partG37c_7_1770
  · exact partG37c_7_1771
  · exact partG37c_7_1772
  · exact partG37c_7_1773
  · exact partG37c_7_1774
  · exact partG37c_7_1775
  · exact partG37c_7_1776
  · exact partG37c_7_1777
  · exact partG37c_7_1778
  · exact partG37c_7_1779
  · exact partG37c_7_1780
  · exact partG37c_7_1781
theorem partG37c_7_1767 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_1768
theorem partG37c_7_1782 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1783 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1784 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1785 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1788 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1789 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1790 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1791 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1792 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1793 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1794 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1795 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1796 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1797 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1798 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1799 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1800 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1787 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_1788
  · exact partG37c_7_1789
  · exact partG37c_7_1790
  · exact partG37c_7_1791
  · exact partG37c_7_1792
  · exact partG37c_7_1793
  · exact partG37c_7_1794
  · exact partG37c_7_1795
  · exact partG37c_7_1796
  · exact partG37c_7_1797
  · exact partG37c_7_1798
  · exact partG37c_7_1799
  · exact partG37c_7_1800
theorem partG37c_7_1786 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_1787
theorem partG37c_7_1801 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1746 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_1747
  · exact partG37c_7_1762
  · exact partG37c_7_1763
  · exact partG37c_7_1764
  · exact partG37c_7_1765
  · exact partG37c_7_1766
  · exact partG37c_7_1767
  · exact partG37c_7_1782
  · exact partG37c_7_1783
  · exact partG37c_7_1784
  · exact partG37c_7_1785
  · exact partG37c_7_1786
  · exact partG37c_7_1801
theorem partG37c_7_1805 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1806 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1807 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1808 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1809 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1810 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1811 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1812 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1813 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1814 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1815 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1816 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1817 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1804 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_1805
  · exact partG37c_7_1806
  · exact partG37c_7_1807
  · exact partG37c_7_1808
  · exact partG37c_7_1809
  · exact partG37c_7_1810
  · exact partG37c_7_1811
  · exact partG37c_7_1812
  · exact partG37c_7_1813
  · exact partG37c_7_1814
  · exact partG37c_7_1815
  · exact partG37c_7_1816
  · exact partG37c_7_1817
theorem partG37c_7_1803 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_1804
theorem partG37c_7_1818 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1819 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1820 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1821 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1822 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1825 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1826 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1827 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1828 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1829 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1830 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1831 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1832 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1833 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1834 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1835 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1836 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1837 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1824 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_1825
  · exact partG37c_7_1826
  · exact partG37c_7_1827
  · exact partG37c_7_1828
  · exact partG37c_7_1829
  · exact partG37c_7_1830
  · exact partG37c_7_1831
  · exact partG37c_7_1832
  · exact partG37c_7_1833
  · exact partG37c_7_1834
  · exact partG37c_7_1835
  · exact partG37c_7_1836
  · exact partG37c_7_1837
theorem partG37c_7_1823 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_1824
theorem partG37c_7_1838 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1839 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1840 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1841 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1844 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1845 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1846 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveGua
