.. index:: ! relaxed memory model

    
.. index:: ! relaxed memory model
Relaxed Memory Model
~~~~~~~~~~~~~~~~~~~~~~

The execution of a WebAssembly program gives rise to a trace of events. WebAssembly’s relaxed memory model constrains the observable behaviours of the program’s execution by defining a consistency condition on the trace of events.

.. _op-time:
.. _syntax-event:

.. math::
   \begin{array}{lll@{\qquad}l}
   \time(act*\ at\ \time_{p}\ \time) &=& time \\
   \end{array}

