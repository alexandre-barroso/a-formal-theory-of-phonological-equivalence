import PhonologicalOpacity.Attenuation.Productive.Baseline.CertificateParts.G37c_0_034
namespace ProductiveGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_0_2805 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","∅","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2778 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_2779
  · exact partG37c_0_2780
  · exact partG37c_0_2781
  · exact partG37c_0_2782
  · exact partG37c_0_2783
  · exact partG37c_0_2784
  · exact partG37c_0_2785
  · exact partG37c_0_2800
  · exact partG37c_0_2801
  · exact partG37c_0_2802
  · exact partG37c_0_2803
  · exact partG37c_0_2804
  · exact partG37c_0_2805
theorem partG37c_0_2809 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2810 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2811 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2812 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2813 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2814 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2815 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2816 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2817 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2818 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2819 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2820 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2821 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2808 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_2809
  · exact partG37c_0_2810
  · exact partG37c_0_2811
  · exact partG37c_0_2812
  · exact partG37c_0_2813
  · exact partG37c_0_2814
  · exact partG37c_0_2815
  · exact partG37c_0_2816
  · exact partG37c_0_2817
  · exact partG37c_0_2818
  · exact partG37c_0_2819
  · exact partG37c_0_2820
  · exact partG37c_0_2821
theorem partG37c_0_2807 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_0_2808
theorem partG37c_0_2822 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2823 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2824 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2825 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2826 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2829 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2830 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2831 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2832 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2833 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2834 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2835 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2836 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2837 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2838 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2839 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2840 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2841 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2828 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_2829
  · exact partG37c_0_2830
  · exact partG37c_0_2831
  · exact partG37c_0_2832
  · exact partG37c_0_2833
  · exact partG37c_0_2834
  · exact partG37c_0_2835
  · exact partG37c_0_2836
  · exact partG37c_0_2837
  · exact partG37c_0_2838
  · exact partG37c_0_2839
  · exact partG37c_0_2840
  · exact partG37c_0_2841
theorem partG37c_0_2827 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_0_2828
theorem partG37c_0_2842 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2843 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2844 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2845 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2848 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2849 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2850 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2851 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2852 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2853 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2854 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2855 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2856 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2857 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2858 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2859 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2860 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2847 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_2848
  · exact partG37c_0_2849
  · exact partG37c_0_2850
  · exact partG37c_0_2851
  · exact partG37c_0_2852
  · exact partG37c_0_2853
  · exact partG37c_0_2854
  · exact partG37c_0_2855
  · exact partG37c_0_2856
  · exact partG37c_0_2857
  · exact partG37c_0_2858
  · exact partG37c_0_2859
  · exact partG37c_0_2860
theorem partG37c_0_2846 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_0_2847
theorem partG37c_0_2861 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2806 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_2807
  · exact partG37c_0_2822
  · exact partG37c_0_2823
  · exact partG37c_0_2824
  · exact partG37c_0_2825
  · exact partG37c_0_2826
  · exact partG37c_0_2827
  · exact partG37c_0_2842
  · exact partG37c_0_2843
  · exact partG37c_0_2844
  · exact partG37c_0_2845
  · exact partG37c_0_2846
  · exact partG37c_0_2861
theorem partG37c_0_2863 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɜ","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2864 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɜ","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2865 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɜ","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2866 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɜ","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2867 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɜ","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2868 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɜ","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2871 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɜ","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2872 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɜ","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2873 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɜ","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2874 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɜ","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2875 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɜ","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2876 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɜ","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2877 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɜ","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2878 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɜ","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2879 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɜ","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2880 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɜ","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2881 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɜ","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2882 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɜ","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2883 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɜ","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2870 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɜ","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_2871
  · exact partG37c_0_2872
  · exact partG37c_0_2873
  · exact partG37c_0_2874
  · exact partG37c_0_2875
  · exact partG37c_0_2876
  · exact partG37c_0_2877
  · exact partG37c_0_2878
  · exact partG37c_0_2879
  · exact partG37c_0_2880
  · exact partG37c_0_2881
  · exact partG37c_0_2882
  · exact partG37c_0_2883
theorem partG37c_0_2869 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɜ","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_0_2870
theorem partG37c_0_2884 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɜ","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveGua
