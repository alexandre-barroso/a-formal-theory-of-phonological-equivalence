                                                                           
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from phonological_grounding.query_discovery import kernel
from phonological_grounding.query_discovery.structures import Skeleton, State


class RefinementPlateauTest(unittest.TestCase):
    def test_delayed_separation_after_an_adjacent_plateau(self):
                                                                               
                                                                               
                                                                            
        skeleton = Skeleton((("a", "a", "a"),), (0,), (None, None, None))
        states = [State(skeleton, ("a", "a", "a")),
                  State(skeleton, ("a", "a", "b"))]
        contexts = [SimpleNamespace(depth=d) for d in range(3)]

        def rotation_trace(_ctx, context, _skeleton):
            return kernel.Trace(skeleton, tuple(
                ("base", (i + context.depth) % 3) for i in range(3)))

        with patch.object(kernel, "enumerate_contexts", return_value=contexts), \
             patch.object(kernel, "context_trace", side_effect=rotation_trace), \
             patch.dict(kernel.BRIDGES, {"first_cell": lambda _ctx, s: s.values[0]}), \
             patch.dict(kernel.BRIDGE_LICENCE, {"first_cell": "fixture"}), \
             patch.dict(kernel.LICENCE_ORDER, {"fixture": 0}):
            result = kernel.graded_refinement(
                None, skeleton, states, ["first_cell"], "fixture", 2)

        self.assertEqual(result.block_counts, [1, 1, 2])
        self.assertEqual(result.first_adjacent_plateau_at, 0)
        self.assertIsNone(result.stabilised_at)
        self.assertEqual(result.witnesses[(0, 1)].depth, 2)
        self.assertNotEqual(result.witnesses[(0, 1)].left,
                            result.witnesses[(0, 1)].right)


if __name__ == "__main__":
    unittest.main()
