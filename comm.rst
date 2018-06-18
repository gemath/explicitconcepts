This module provides explicit concepts and an ``implements``-relation
between concepts and implementing types.

Motivation
==========

A type satisfies a regular concept if it matches the requirements defined
by the concept. This is an implicit match, the creator of the type did
not declare intent to make the type satisfy the concept. While this is often
useful, in other cases, stating an ``implements``-relation between the
type and the concept in the source code to make the intention clear produces
more readable and safer code: An explicit concept is only satisfied by a
type if such an ``implements``-relation exists.

Use
====

.. code-block:: nim
  implements C, ExC: X
Defines ``implements``-relations for an existing type and existing concepts:
``X`` implements concepts ``C`` and ``ExC``.

.. code-block:: nim
  explicit:
    type
      ExD = concept d
        d.x is float
Defines an explicit concept ``ExD``.

.. code-block:: nim
  implements ExD:
    type
      Xx = object
        x: float
  
      Y = object
        x: float

  type
    Y2 = object
      x: float

  echo(Y is ExD)   # -> true
  echo(Y2 is ExD)  # -> false
Defines ``implements``-relations for new types: ``Xx`` and ``Y``
implement concept ``ExD``. Note that, despite the fact that it fulfills
the requirement in the body of ``ExD``, ``Y2`` does not satisfy ``ExD``
because ``ExD`` is explicit and there is no ``implements``-relation
defined between the two. 

The ``implements``-relation between a type and a concept automatically
extends to aliases of the two and to derivatives of the type, but not to
distinct aliases of the two and to refinements of the concept.

For details see the source files in the ``tests`` directory.
