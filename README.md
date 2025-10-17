# SPTG

Symbolic Path-Guided Test Case Generator



Using SPTG

```
sptg.exe 

```


**Example01 -- Simple timed system (no symbolic data)**



**XLIA subset to encode timed symbolic transition system**


```
// ============================================================
// Prologue - Header
// ============================================================
@xlia< system , 1.0 >:

// ============================================================
// System Definition
// ============================================================
timed system S {

    // ========================================================
    // Composite Part: State Machine Definition
    // ========================================================
    @composite:
    statemachine SM {
        @public:

            // ----------------------------------------------
            // Declaration of Ports
            // ----------------------------------------------
            port input  In;
            port output Done;
            port input  In1( urational );
            port input  In2( integer );
            port output Out( urational );

            // Declaration of N-ary Ports
            port input  In3( bool, integer, rational );
            port output Out2( integer, bool );

            // ----------------------------------------------
            // Declaration of Constants
            // ----------------------------------------------
            const integer N = 42;

        @private:

            // ----------------------------------------------
            // Declaration of Variables
            // ----------------------------------------------
            var urational sum;
            var urational x;
            var urational y;
            var integer   z;
            var bool      flag;
            var integer   fee;

            // ----------------------------------------------
            // Declaration of Clocks
            // ----------------------------------------------
            var clock urational cl;
            var clock urational cl2;

        // ====================================================
        // Behavioral Description: States and Transitions
        // ====================================================
        @region:

            // ----------------------------------------------
            // Initial State
            // ----------------------------------------------
            state<start> q0 {
                @init {
                    sum  := 0;
                    flag := false;
                    guard( fee > 0 );
                }

                transition tr1 --> q1 {
                    input In1( x );
                    guard ( 1 <= x <= 10 );
                    sum := sum + x;
                    y   := sum;
                    cl  := 0;
                }

                transition tr2 --> q1 {
                    input In( x );
                    guard ( 10 < x && x < N );
                    {|,|
                        sum := sum + x;
                        y   := sum; // y receives the pre-increment sum value
                    }
                    cl2 := 0;
                }
            }

            // ----------------------------------------------
            // Secondary State
            // ----------------------------------------------
            state q1 {
                transition tr3 --> q0 {
                    guard( x <= 10 && cl == N - x );
                    output Out( sum - 1 );
                }

                transition tr4 --> q0 {
                    guard( x > 10 );
                    guard( cl <= 5 );
                    output Out2( fee, flag );
                    flag := true;
                    cl2 := 0;
                }

                transition tr5 --> q2 {
                    guard( sum >= 15 && cl2 <= 1 );
                    output Done;
                    cl2 := 0;
                }
            }

            // ----------------------------------------------
            // Terminal State
            // ----------------------------------------------
            state q2;

        // ====================================================
        // Communication Part: Port Connections
        // ====================================================
        @com:
        connect< env > {
            input  In;
            input  In1;
            input  In2;
            input  In3;
            output Done;
            output Out;
            output Out2;
        }
    }
}

```

@startuml

	' allow_mixing
	' !pragma teoz true

	skinparam componentstyle uml2

	hide empty description

	skinparam linetype polyline
	' skinparam linetype ortho
	' left to right direction
	!function $kw($key_word)
	!return "**<color blue>" + $key_word + "</color>**"
	!endfunction
	!function $kop($key_operator)
	!return "**<color blue>" + $key_operator + "</color>**"
	!endfunction
	!function $ks($key_symbol)
	!return "**<color blue>" + $key_symbol + "</color>**"
	!endfunction
	!function $param($p)
	!return "**<color darkred>" + $p + "</color>**"
	!endfunction
	!$natural = "**<color darkred>&#9838;</color>**"

	!$tp_path = "#Green,thickness=2"

	<style>
		note {
			backgroundcolor white
			shadowing 0
			linecolor transparent
		}
	</style>

	skinparam backgroundColor White

	skinparam state {
		StartColor Green
		EndColor Red
		'Attribut pour les transitions
		ArrowColor Black
		ArrowColor<< Else >> Orange
		'Attribut par défaut pour les états
		BorderColor Gray
		BackgroundColor Wheat
		'Attribut pour les états composites
		BackgroundColor<< System       >> Turquoise
		BackgroundColor<< Statemachine >> DodgerBlue
		BackgroundColor<< Machine      >> SpringGreen
		BackgroundColor<< Instance     >> Orchid
		BackgroundColor<< Composite    >> SpringGreen
		'Attribut pour les états simples
		BackgroundColor<< simple_hierarchic >> PaleTurquoise
		BackgroundColor<< simple >> PaleTurquoise
		BackgroundColor<< start  >> Green
		BackgroundColor<< final >> Red
		BackgroundColor<< pass >> GreenYellow
		BackgroundColor<< sync   >> Aqua
		'Attribut pour les pseudo-états
		BackgroundColor<< pseudostate >> Lavender
		BackgroundColor<< initial     >> GreenYellow
		BackgroundColor<< junction    >> GreenYellow
		BackgroundColor<< choice      >> Orange
		BackgroundColor<< fork        >> SpringGreen
		BackgroundColor<< junction    >> SpringGreen
		BackgroundColor<< dhistory    >> SpringGreen
		BackgroundColor<< shistory    >> SpringGreen
		BackgroundColor<< return      >> OrangeRed
		BackgroundColor<< terminal    >> DarkGray
		FontColor Black
		FontName Times
		FontSize 14
	}

state "**timed system** S" as S_1405366479 << System >> {

	state "**statemachine** SM" as SM_281118486 << Statemachine >> {

		state "q0" as q0_201018752 << start >>

		note bottom of q0_201018752 #white
			**init( )**
			sum $kop(":=") 0 $ks(";")
			flag $kop(":=") false $ks(";")
			$kw("guard") (fee $kop(">") 0) $ks(";")
		end note

		q0_201018752 --> q1_357179108

		note on link #white
			**tr1** 
			$kw("input") In1(x) $ks(";")
			$kw("guard") ((1 $kop("<=") x) <= 10) $ks(";")
			sum $kop(":=") (sum $kop("+") x) $ks(";")
			y $kop(":=") sum $ks(";")
			cl $kop(":=") 0 $ks(";")
		end note

		q0_201018752 --> q1_357179108

		note on link #white
			**tr2** 
			$kw("input") In(x) $ks(";")
			$kw("guard") ((10 $kop("<") x)
				$kop("&&") (x $kop("<") N)) $ks(";")
			$ks("{")$ks("|,|")
				sum $kop(":=") (sum $kop("+") x) $ks(";")
				y $kop(":=") sum $ks(";")
			$ks("}")
			cl2 $kop(":=") 0 $ks(";")
		end note

		

		state "q1" as q1_357179108 << simple >>

		q1_357179108 --> q0_201018752

		note on link #white
			**tr3** 
			$kw("guard") ((x $kop("<=") 10)
				$kop("&&") (cl $kop("==") (N $kop("-") x))) $ks(";")
			$kw("output") Out((sum $kop("-") 1)) $ks(";")
		end note

		q1_357179108 --> q0_201018752

		note on link #white
			**tr4** 
			$kw("guard") (x $kop(">") 10) $ks(";")
			$kw("guard") (cl $kop("<=") 5) $ks(";")
			$kw("output") Out2(fee, flag) $ks(";")
			flag $kop(":=") true $ks(";")
			cl2 $kop(":=") 0 $ks(";")
		end note

		q1_357179108 --> q2_1367554826

		note on link #white
			**tr5** 
			$kw("guard") ((sum $kop(">=") 15)
				$kop("&&") (cl2 $kop("<=") 1)) $ks(";")
			$kw("output") Done $ks(";")
			cl2 $kop(":=") 0 $ks(";")
		end note

		state "q2" as q2_1367554826 << simple >>

	}

	note bottom of SM_281118486
	{{
	title "Model of Interaction : list of connections"
	== connect< env > ==
	' group connect< env >
		?-> SM : In
		?-> SM : In1
		?-> SM : In2
		?-> SM : In3
		SM ->? : Done
		SM ->? : Out
		SM ->? : Out2
	' end group
	}}
	end note
}



@enduml



