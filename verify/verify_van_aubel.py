"""Numerically test the even-dimensional Van Aubel identity.

This is a randomized consistency check, not a mathematical proof.  It tests
both orientations, several even dimensions, arbitrary orthogonal complex
structures, and explicit degenerate configurations.
"""

from __future__ import annotations

import argparse
from collections.abc import Iterable

import numpy as np
from numpy.typing import NDArray


Vector = NDArray[np.float64]
Matrix = NDArray[np.float64]


def standard_complex_structure(dimension: int) -> Matrix:
    """Return diag(J_2, ..., J_2), where J_2(x, y) = (-y, x)."""
    if dimension <= 0 or dimension % 2 != 0:
        raise ValueError("dimension must be a positive even integer")

    block = np.array([[0.0, -1.0], [1.0, 0.0]])
    return np.kron(np.eye(dimension // 2), block)


def random_complex_structure(dimension: int, rng: np.random.Generator) -> Matrix:
    """Return Q J_0 Q^T for a random orthogonal matrix Q."""
    q, _ = np.linalg.qr(rng.normal(size=(dimension, dimension)))
    j = q @ standard_complex_structure(dimension) @ q.T

    identity = np.eye(dimension)
    np.testing.assert_allclose(j @ j, -identity, atol=1e-12, rtol=1e-12)
    np.testing.assert_allclose(j.T @ j, identity, atol=1e-12, rtol=1e-12)
    return j


def square_center(x: Vector, y: Vector, j: Matrix, epsilon: int) -> Vector:
    """Return the center of the square built on the directed edge XY."""
    return (x + y + epsilon * (j @ (y - x))) / 2.0


def verify_configuration(
    points: Vector,
    j: Matrix,
    epsilon: int,
    *,
    tolerance: float = 1e-10,
) -> None:
    """Check the identity, equal-length conclusion, and orthogonality."""
    if points.shape != (4, j.shape[0]):
        raise ValueError("points must have shape (4, dimension)")
    if epsilon not in (-1, 1):
        raise ValueError("epsilon must be +1 or -1")

    a, b, c, d = points
    p = square_center(a, b, j, epsilon)
    q = square_center(b, c, j, epsilon)
    r = square_center(c, d, j, epsilon)
    s = square_center(d, a, j, epsilon)

    pr = r - p
    qs = s - q

    np.testing.assert_allclose(pr, epsilon * (j @ qs), atol=tolerance, rtol=tolerance)
    np.testing.assert_allclose(
        np.linalg.norm(pr),
        np.linalg.norm(qs),
        atol=tolerance,
        rtol=tolerance,
    )

    dot_tolerance = tolerance * (1.0 + np.linalg.norm(pr) * np.linalg.norm(qs))
    if abs(float(pr @ qs)) > dot_tolerance:
        raise AssertionError(
            f"orthogonality failed: PR·QS={float(pr @ qs):.16g}, "
            f"allowed error={dot_tolerance:.3g}"
        )


def degenerate_configurations(dimension: int) -> Iterable[Vector]:
    """Yield configurations with coincident points, zero edges, and collinearity."""
    zero = np.zeros(dimension)
    e1 = np.zeros(dimension)
    e1[0] = 1.0

    yield np.stack([zero, zero, zero, zero])
    yield np.stack([zero, zero, e1, -2.0 * e1])
    yield np.stack([-2.0 * e1, -0.5 * e1, 1.5 * e1, 4.0 * e1])


def run_checks(
    dimensions: Iterable[int],
    trials: int,
    seed: int,
    tolerance: float,
) -> int:
    rng = np.random.default_rng(seed)
    total = 0

    for dimension in dimensions:
        # Degenerate cases use the standard J so their structure is reproducible.
        j0 = standard_complex_structure(dimension)
        for points in degenerate_configurations(dimension):
            for epsilon in (-1, 1):
                verify_configuration(points, j0, epsilon, tolerance=tolerance)
                total += 1

        # Each trial uses a new orthogonal conjugate of the standard J.
        for _ in range(trials):
            j = random_complex_structure(dimension, rng)
            points = rng.normal(size=(4, dimension))
            for epsilon in (-1, 1):
                verify_configuration(points, j, epsilon, tolerance=tolerance)
                total += 1

    return total


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Randomized verification of the even-dimensional Van Aubel identity."
    )
    parser.add_argument(
        "--dimensions",
        type=int,
        nargs="+",
        default=[2, 4, 6, 10, 20],
        help="positive even dimensions to test",
    )
    parser.add_argument("--trials", type=int, default=500, help="random trials per dimension")
    parser.add_argument("--seed", type=int, default=20260802, help="random seed")
    parser.add_argument("--tolerance", type=float, default=1e-10)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if args.trials < 0:
        raise ValueError("trials must be nonnegative")

    total = run_checks(args.dimensions, args.trials, args.seed, args.tolerance)
    print(f"All {total} checks passed.")


if __name__ == "__main__":
    main()
