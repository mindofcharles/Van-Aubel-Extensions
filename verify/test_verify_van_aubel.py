"""Deterministic boundary and expected-failure tests for the NumPy checker."""

from __future__ import annotations

import unittest

import numpy as np

from verify_van_aubel import (
    square_center,
    standard_complex_structure,
    verify_configuration,
)


class InputValidationTests(unittest.TestCase):
    def test_standard_structure_rejects_zero_dimension(self) -> None:
        with self.assertRaises(ValueError):
            standard_complex_structure(0)

    def test_standard_structure_rejects_odd_dimension(self) -> None:
        with self.assertRaises(ValueError):
            standard_complex_structure(3)

    def test_configuration_rejects_non_sign(self) -> None:
        points = np.zeros((4, 2))
        with self.assertRaises(ValueError):
            verify_configuration(points, standard_complex_structure(2), 0)

    def test_configuration_rejects_wrong_shape(self) -> None:
        points = np.zeros((3, 2))
        with self.assertRaises(ValueError):
            verify_configuration(points, standard_complex_structure(2), 1)


class ExpectedFailureTests(unittest.TestCase):
    def test_nonorthogonal_complex_structure_fails_metric_check(self) -> None:
        j = np.array([[0.0, -2.0], [0.5, 0.0]])
        np.testing.assert_allclose(j @ j, -np.eye(2))
        points = np.array(
            [[0.0, 0.0], [1.0, 0.0], [1.0, 1.0], [0.0, 1.0]]
        )
        with self.assertRaises(AssertionError):
            verify_configuration(points, j, 1)

    def test_mixed_edge_signs_fail_the_uniform_identity(self) -> None:
        j = standard_complex_structure(2)
        a, b, c, d = np.array(
            [[0.0, 0.0], [2.0, 1.0], [-1.0, 3.0], [4.0, -2.0]]
        )
        p = square_center(a, b, j, 1)
        q = square_center(b, c, j, -1)
        r = square_center(c, d, j, 1)
        s = square_center(d, a, j, 1)
        self.assertFalse(np.allclose(r - p, j @ (s - q)))


if __name__ == "__main__":
    unittest.main()
