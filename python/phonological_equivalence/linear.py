from __future__ import annotations

from fractions import Fraction
from typing import Any

from .rational import ParseRational, RationalText


Matrix = list[list[Fraction]]


def ParseMatrix(value: list[list[Any]]) -> Matrix:
    matrix = [[ParseRational(cell) for cell in row] for row in value]
    if matrix and any(len(row) != len(matrix[0]) for row in matrix):
        raise ValueError("Ragged matrix")
    return matrix


def EncodeMatrix(value: Matrix) -> list[list[str]]:
    return [[RationalText(cell) for cell in row] for row in value]


def Identity(size: int) -> Matrix:
    return [[Fraction(int(row == column)) for column in range(size)] for row in range(size)]


def Transpose(value: Matrix) -> Matrix:
    if not value:
        return []
    return [list(column) for column in zip(*value, strict=True)]


def Multiply(left: Matrix, right: Matrix) -> Matrix:
    if not left or not right:
        return []
    if len(left[0]) != len(right):
        raise ValueError("Matrix dimensions do not compose")
    columns = Transpose(right)
    return [[sum(a * b for a, b in zip(row, column, strict=True)) for column in columns] for row in left]


def RowReduce(value: Matrix) -> tuple[Matrix, list[int]]:
    matrix = [row[:] for row in value]
    pivots: list[int] = []
    row = 0
    width = len(matrix[0]) if matrix else 0
    for column in range(width):
        pivot = next((index for index in range(row, len(matrix)) if matrix[index][column] != 0), None)
        if pivot is None:
            continue
        matrix[row], matrix[pivot] = matrix[pivot], matrix[row]
        scale = matrix[row][column]
        matrix[row] = [cell / scale for cell in matrix[row]]
        for index in range(len(matrix)):
            if index != row and matrix[index][column] != 0:
                factor = matrix[index][column]
                matrix[index] = [cell - factor * pivot_cell for cell, pivot_cell in zip(matrix[index], matrix[row], strict=True)]
        pivots.append(column)
        row += 1
        if row == len(matrix):
            break
    return matrix, pivots


def Rank(value: Matrix) -> int:
    return len(RowReduce(value)[1])


def Determinant(value: Matrix) -> Fraction:
    size = len(value)
    if any(len(row) != size for row in value):
        raise ValueError("Determinant requires a square matrix")
    matrix = [row[:] for row in value]
    determinant = Fraction(1)
    for column in range(size):
        pivot = next((index for index in range(column, size) if matrix[index][column] != 0), None)
        if pivot is None:
            return Fraction(0)
        if pivot != column:
            matrix[column], matrix[pivot] = matrix[pivot], matrix[column]
            determinant = -determinant
        pivot_value = matrix[column][column]
        determinant *= pivot_value
        for index in range(column + 1, size):
            factor = matrix[index][column] / pivot_value
            for offset in range(column, size):
                matrix[index][offset] -= factor * matrix[column][offset]
    return determinant


def Symmetric(value: Matrix) -> bool:
    return all(value[row][column] == value[column][row] for row in range(len(value)) for column in range(len(value))) if all(len(row) == len(value) for row in value) else False


def PrincipalSubmatrix(value: Matrix, indices: tuple[int, ...]) -> Matrix:
    return [[value[row][column] for column in indices] for row in indices]


def PositiveSemidefinite(value: Matrix) -> bool:
    if not Symmetric(value):
        return False
    size = len(value)
    for mask in range(1, 1 << size):
        indices = tuple(index for index in range(size) if mask & (1 << index))
        if Determinant(PrincipalSubmatrix(value, indices)) < 0:
            return False
    return True
