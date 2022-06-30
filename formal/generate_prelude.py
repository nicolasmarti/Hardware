
prelude = """
theory Map

type map 'a 'b
function ([]) (map 'a 'b) (x: 'a): 'b
function ([<-]) (map 'a 'b) (x: 'a) (y: 'b): map 'a 'b

axiom map_update1: forall m: map 'a 'b, x: 'a, y: 'b.
      		   forall e: 'a. e = x -> m[x<-y][e] = y
axiom map_update2: forall m: map 'a 'b, x: 'a, y: 'b.
      		   forall e: 'a. e <> x -> m[x<-y][e] = m[e]

axiom map_eq_ext: forall m1 m2: map 'a 'b.
      	      (forall x: 'a. m1[x] = m2[x]) -> m1 = m2

lemma map_eq: forall m1 m2: map 'a 'b.
      	      m1 = m2 -> (forall x: 'a. m1[x] = m2[x])

lemma update_eq: forall m: map 'a 'b, x: 'a. m[ x <- m[x] ] = m

function cste (y: 'b): map 'a 'b
axiom cste_sem: forall y: 'b, x: 'a. (cste y)[x] = y

lemma map_update_update_eq: forall m: map 'a 'b,
      x1 x2: 'a, y1 y2: 'b.
      x1 = x2 ->
      m[ x1 <- y1 ][ x2 <- y2 ] = m[ x2 <- y2 ]

lemma map_update_update_eq2: forall m: map 'a 'b,
      x: 'a, y1 y2: 'b.
      m[ x <- y1 ][ x <- y2 ] = m[ x <- y2 ]

lemma map_update_update_swap: forall 
      x1 x2: 'a, y1 y2: 'b, m: map 'a 'b.
      x1 <> x2 ->
      m[ x2 <- y2 ][ x1 <- y1 ] = m[ x1 <- y1 ][ x2 <- y2 ]

lemma map_update_update_inj: forall m1 m2: map 'a 'b,
      x1 x2: 'a, y1 y2: 'b.
      x1 = x2 -> y1 = y2 ->
      m1 = m2 ->
      m1[ x1 <- y1 ] = m2[ x2 <- y2 ]

lemma helper_map1:
      forall m1 m2: map 'a 'b,
             x1 x2: 'a, y1 y2 y3: 'b.
             x1 <> x2 ->
             y2 = y3 ->
             m2 = m1[ x1 <- y1 ] ->
             m2[ x2 <- y3 ] = m1[ x2 <- y2 ][ x1 <- y1 ]

end

theory Power2

use int.Int

function power2 (n: int): int
axiom power2_0: power2 0 = 1
axiom power2_n: forall n: int. n > 0 -> power2 n = 2 * power2 (n-1)
axiom power2_pos: forall n: int. n >= 0 -> power2 n > 0

axiom power2_eq: forall n1 n2: int. power2 n1 = power2 n2 -> n1 = n2
axiom power2_neq: forall n1 n2: int. power2 n1 <> power2 n2 -> n1 <> n2

function bit2int (n:int) (b: bool): int = if b then power2 n else 0

axiom power2_monotonic:
    forall n m:int. 0 <= n < m -> power2 n < power2 m
axiom power2_inj:
    forall n m:int. power2 n = power2 m -> n = m
    
end

theory Wire

use int.Int
use bool.Bool
use Map

type wire = map int bool

constant wfalse: wire
axiom wfalse_ax: forall t: int. wfalse[t] = false

constant wtrue: wire
axiom wtrue_ax: forall t: int. wtrue[t] = true

end

theory Nand
use Map
use Wire
use bool.Bool

function a: wire
function b: wire
function out: wire
axiom sem: forall t: int. out[t] = notb (andb a[t] b[t])

end

theory DFF

use Map
use int.Int
use bool.Bool
use Wire

function _in: wire
function out: wire

type st = bool

function state: map int st

axiom output: forall t: int. out[t+1] = state[t]
axiom transition: forall t: int. state[t] = _in[t]

end

"""

def generate_BinX( n ):
    script = list()

    script.append( "theory Bin%d" % n )
    
    script += [ "use %s" % x for x in
                [ "int.Int", "bool.Bool", "Map", "Power2" ]
    ]

    script.append( "type d%d = <range 0 %d>" % (n, n-1) )

    script.append( "meta coercion function d%d'int" % n )

    s = "lemma d%d_destruct: forall x: d%d. " % (n, n)
    s += " \/ ".join( [
        "x = (%d:d%d)" % (x, n)
        for x in range( 0, n )
    ])
    script.append( s )

    script.append( "type bin%d = map d%d bool" % (n, n) )

    script.append(
        "lemma bin%d_eq: forall b1 b2: bin%d. (forall d: d%d. b1[d] = b2[d]) -> b1 = b2" % (n, n, n)
    )
    
    s = "function bin%d_uint (b: bin%d): int = " % (n, n)
    s += " + ".join( [
        "bit2int %d b[%d:d%d]" % (x, x, n)
        for x in range( 0, n )
    ])
    script.append( s )

    script.append( "lemma bin%d_uint_bound: forall b: bin%d. 0 <= bin%d_uint b <= power2 %d - 1" % (n,n,n,n) )

    script.append(
        "function bin%d_sint (b: bin%d): int = bin%d_uint b - (if b[%d:d%d] then power2 %d else 0) " % (n,n,n,n-1,n,n)
    )

    script.append(
        "lemma bin%d_sint_bound: forall b: bin%d. - power2 %d <= bin%d_sint b <= power2 %d - 1" % (n, n, n-1, n, n-1)
    )

    
    script.append(
"""lemma bin%d_uint_eq_1: forall b1 b2: bin%d.
(forall d: d%d. b1[d] = b2[d]) -> bin%d_uint b1 = bin%d_uint b2""" % (n, n, n, n, n)
    )

    script.append(
"""lemma bin%d_uint_eq_2: forall b1 b2: bin%d.
bin%d_uint b1 = bin%d_uint b2 -> (forall d: d%d. b1[d] = b2[d])""" % (n, n, n, n, n)
    )

    script.append(
        """
lemma bin%d_uint_not: forall b1 b2: bin%d.
(forall d: d%d. b1[d] = notb b2[d]) -> bin%d_uint b1 = power2 %d - 1 - bin%d_uint b2""" % (n, n, n, n, n, n)
    )

    script.append(
"""lemma bin%d_sint_eq_1: forall b1 b2: bin%d.
(forall d: d%d. b1[d] = b2[d]) -> bin%d_sint b1 = bin%d_sint b2""" % (n, n, n, n, n)
    )

    script.append(
"""lemma bin%d_sint_eq_2: forall b1 b2: bin%d.
bin%d_sint b1 = bin%d_sint b2 -> (forall d: d%d. b1[d] = b2[d])""" % (n, n, n, n, n)
    )
    
    script.append(
        """
lemma bin%d_sint_not: forall b1 b2: bin%d.
(forall d: d%d. b1[d] = notb b2[d]) -> bin%d_sint b1 + bin%d_sint b2 = -1""" % (n, n, n, n, n)
    )

    script.append( "constant one%d: bin%d" % (n,n) )
    s = "axiom one%d_def: forall d: d%d. " % (n, n)
    s += "(d = (0:d%d) -> one%d[d] = true) /\ (d <> (0:d%d) -> one%d[d] = false)" % (n, n, n, n)
    
    script.append( s )
    script.append( "lemma one%d_uint: bin%d_uint one%d = 1" % (n, n, n) )
    script.append( "lemma one%d_sint: bin%d_sint one%d = 1" % (n, n, n) )

    script.append( "constant zero%d: bin%d" % (n,n) )
    s = "axiom zero%d_def: forall d: d%d. zero%d[d] = false" % (n, n, n)
    script.append( s )
    script.append( "lemma zero%d_uint: bin%d_uint zero%d = 0" % (n, n, n) )
    script.append( "lemma zero%d_sint: bin%d_sint zero%d = 0" % (n, n, n) )

    script.append( "constant trues%d: bin%d" % (n,n) )
    s = "axiom trues%d_def: forall d: d%d. trues%d[d] = true" % (n, n, n)
    script.append( s )
    script.append( "lemma trues%d_uint: bin%d_uint trues%d = power2 %d - 1" % (n, n, n, n) )
    script.append( "lemma trues%d_sint: bin%d_sint trues%d = -1" % (n, n, n) )

    script.append( "type wire%d = map int bin%d" % (n, n) )

    script.append(
        """
constant wone%d: wire%d
axiom wone%d_def: forall t: int. wone%d[t] = one%d
constant wzero%d: wire%d
axiom wzero%d_def: forall t: int. wzero%d[t] = zero%d
constant wtrues%d: wire%d
axiom wtrues%d_def: forall t: int. wtrues%d[t] = trues%d
        """ % ((n, n, n, n, n) * 3)
    )

    script.append(
        """
function not%d (b: bin%d): bin%d
axiom not%d_def: forall b: bin%d, x: d%d. (not%d b)[x] = notb b[x]
lemma not%d_inv: forall b: bin%d. not%d (not%d b) = b (* might need map_eq_ext *)
lemma not%d_inj: forall b1 b2: bin%d. not%d b1 = not%d b2 -> b1 = b2

lemma bin%d_uint_not%d: forall b: bin%d.
      bin%d_uint (not%d b) = power2 %d - 1 - bin%d_uint b
lemma bin%d_sint_not%d: forall b: bin%d.
      bin%d_sint (not%d b) = -( 1 + bin%d_sint b )

lemma not%d_zero%d: not%d zero%d = trues%d
lemma not%d_trues%d: not%d trues%d = zero%d

        """ % ((n,) * 38)
    )

    script.append(
        """
function and%d (b1 b2: bin%d): bin%d
axiom and%d_def: forall b1 b2: bin%d, x: d%d. (and%d b1 b2)[x] = andb b1[x] b2[x]
lemma and%d_comm: forall b1 b2: bin%d. and%d b1 b2 = and%d b2 b1
lemma and%d_trues%d: forall b: bin%d. and%d b trues%d = b
lemma and%d_zero%d: forall b: bin%d. and%d b zero%d = zero%d
        """ % ((n,) * 22)
    )

    script.append(
        """
function or%d (b1 b2: bin%d): bin%d
axiom or%d_def: forall b1 b2: bin%d, x: d%d. (or%d b1 b2)[x] = orb b1[x] b2[x]
lemma or%d_comm: forall b1 b2: bin%d. or%d b1 b2 = or%d b2 b1
lemma or%d_trues%d: forall b: bin%d. or%d b trues%d = trues%d
lemma or%d_zero%d: forall b: bin%d. or%d b zero%d = b
        """ % ((n,) * 22)
    )

    script.append(
        """
lemma not%d_or%d_and%d: forall b1 b2: bin%d.
      not%d (or%d b1 b2) = and%d (not%d b1) (not%d b2)
lemma not%d_and%d_or%d: forall b1 b2: bin%d.
      not%d (and%d b1 b2) = or%d (not%d b1) (not%d b2)

lemma bin%d_sint_trues%d: bin%d_sint trues%d = - 1
lemma bin%d_uint_trues%d: bin%d_uint trues%d = power2 %d - 1
        """ % ((n,) * 27)
    )

    script.append(
        """
function uint_bin%d(i: int): bin%d
axiom uint_bin%d_sem: forall i: int.
      0 <= i <= power2 %d - 1 -> bin%d_uint( uint_bin%d( i ) ) = i
        """ % (n, n, n, n, n, n)
    )

    script.append(
        ("function lit%d ( " + (" ".join([ "b%d" % x for x in range(0, n ) ])) + ": bool ): bin%d") % (n, n)
    )

    script.append(
        "axiom lit%d_sem: forall " % n +
        (" ".join([ "b%d" % x for x in range(0, n ) ])) +
        ": bool. " +
        (" /\ ".join([
            ("(lit%d "+ (" ".join([ "b%d" % y for y in range(0, n ) ])) + ")[%d:d%d] = b%d" ) % (n, x, n, x)
            for x in range(0, n )
        ]))

    )

    script.append(
        ("lemma lit%d_proj: forall b: bin%d. b = lit%d " +
         " ".join( [ "b[%d:d%d]" % (x, n) for x in range(0, n) ] )
        ) % (n, n, n)
    )
    
    
    script.append( "end" )

    #############
    
    script.append( "theory Wire%d" % n )

    script.append(
        """
use Wire
use Bin%d
use Map
        """ % n
    )
    script.append( "function w: wire%d" % n )

    for x in range( 0, n ):
        script.append(
            """ 
function w%d: wire
axiom ax%d: forall t: int. w[t][%d:d%d] = w%d[t]
            """ % (x, x, x, n, x)
        )
        
    
    script.append( "end" )

    
    return "\n".join( script )

if __name__ == "__main__"    :

    print prelude

    for x in range( 2, 17 ):
        print generate_BinX( x )

    
