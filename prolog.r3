;; ============================================
;; Script: prolog.r
;; downloaded from: www.REBOL.org
;; on: 27-May-2013
;; at: 9:32:14.482698 UTC
;; owner: coccinelle [script library member who
;; can update this script]
;; ============================================
;; ==================================================
;; email address(es) have been munged to protect them
;; from spam harvesters.
;; If you were logged on the email addresses would
;; not be munged
;; ==================================================
REBOL [
    Title: "Prolog Like Inference Engine" 
    Date: 08-sep-2005
    Name: "PROLOG"
    Version: 1.7
    File: %prolog.r
    Author: "Marco"
    Category: []
    Library: [
        level: 'intermediate
        platform: 'all
        type: [dialect tool function]
        domain: [dialects ai]
        tested-under: [win]
        support: %mvri--bluewin--ch
        license: public-domain
        see-also: none
    ]
    
    History: [
        {1.0 Initial version}
        {1.1 Perfomrance improvement}
        {1.2 Refactoring of unify and call?}
        {1.3 English translation for www.rebol.org publication}
        {1.4 Change misspelled wich by which (thanks Sunanda)}
        {1.5 Correction of a small bug which appears with wiew 1.3}
        {1.6 Correction of a small bug thanks to Martin}
        {1.7 Add CALL hardcoded predicate and diagnostic (trial) engine}
    ]
    Purpose: {
        This is an inference engine wich process prolog like clause
        The engine can process prolog like clauses of the form :
            man [jean]
            woman [mary]
            human [X] [man [X]]
            human [X] [woman [X]]

        CUT (!) and FAIL are implemanted (it's the only hardcoded predicates in the engine)

        The engine execute Rebol code placed in parenthesis (like in the parse function).
        Parenthesis can be place either in the body of the clause
        or as a parameter of predicates :
            add [X Y (X + Y)]
            human [X] [man [X] (print [X "is a human"])]

        The engine consider that all words with a value that are not functions as vars.
        Other words are taken as symbol.

        Local vars are all words that start with an uppercase char or with underscore (_)
        The anonyme var is implemented and can be either _ or none

        A var is free if it's value is none, a var is bound if it's value is not none

        The engine offers a set of pre-defined clauses (internal clausses)
        like NOT, EQUAL?, IF, BOUND, FREE and REPEAT.

        To add or remove clauses from a knowlege base use ASSERT and RETRACT function

        To execute a goal, use GOAL or FOR-WHICH functions

        To bench the engine use BENCH-GOAL function.

        The call-trace and unify-trace words allows to enable or disable the trace capability of the engine.
    }
]

; **********************************************************************************
; * Public interface.
; -------------------
; - assert          allows you to add clauses to the knowledge
; - retract         allows you to retract clauses from the knowledge base
; - goal            allows you to get all the possible solution for a goal
; - for-which       allows you to execute a block for each solution of the goal
; - bench-goal      allows you to get the time to obtain all the solution for a goal
; - call-trace      allows you to enable or disable the trace of goal calls
; - unify-trace     allows you to enable or disable the trace of clause unification
; **********************************************************************************

assert: retract: goal: for-which: bench-goal: none

if not value? 'call-trace [call-trace: false]
if not value? 'unify-trace [unify-trace: false]


context compose [
; *******************
; * ASSERT function *
; *******************
;
; This function parse a block of clauses, transform it in a intenal form
; and append it to the knowledge base.
;
; The function creates a new base if none is passed as argument
;
; The internal format is a block that is directly used to make the call object.
;
; The parsing is done only to find the clauses but doesn't ckeck the validity of the body of the clause
; *****************************************************************************************************

    set 'assert func [
        "Create or update a KB block with parsed clauses. Return the KB block."
        base [block! none!] "KB block or none for a new base"
        clauses [block!] "Clauses block to be parsed"
        /local rule name pattern goals clause
    ][
        rule: [
            ['comment string!]
        |
            [name: word! pattern: block! goals: block! (
                append-clause base to-word first name first pattern first goals
            )]
        |
            [name: word! pattern: block! (
                append-clause base to-word first name first pattern []
            )]
        ]
        if none? base [
            base: copy []
        ]
        if not parse clauses [some rule] [
            make error! "Invalid clauses"
        ]
        base
    ]

; ********************
; * RETRACT function *
; ********************
;
; This function rectract a clause from the knowledge base
;
; This function isn't completely tested and there is perhaps some bugs in it.
; ***************************************************************************

    set 'retract func [
        "Retract a clause from the block"
        base [block!] "The KB block"
        predicat [block!] "The predicate to retract"
        /all
        /local result p
    ][
        result: base
        name: pick predicat 1
        if system/words/all [
            clause-var? name
            p: get name
        ][
            name: p
        ]
        either any [
            equal? '_ name
            clause-var? name 
        ][
            while [not empty? base] [
                either remove-clause second base predicat all [
                    if empty? second base [
                        remove/part base 2
                    ]
                    if not all [
                        break
                    ]
                ][
                    base: skip base 2
                ]
            ]
        ][
            while [not none? base: find/skip base name 2][
                either remove-clause second base predicat all [
                    if empty? second base [
                        remove/part base 2
                    ]
                    if not all [
                        break
                    ]
                ][
                    base: skip base 2
                ]
            ]
        ]
        result
    ]

; This is the model of the call object
; ************************************

    clause: make object! [
        predicat: []         ; the head of the clause
        goals: []            ; the body of the clause
        vars: []             ; the list of the locaql vars of the clause
    
        save-predicat: none  ; the saved head of the clause (used only for trace)
        save-vars: none      ; the saved vars values (restored just before to recall the gaol)


        curr-goal: []        ; The surrent sub-goal
        curr-goals: none     ; The current list of sub-goal
        curr-vars: none      ; the current vars values
        curr-clauses: none   ; the current matched clause list
        curr-call: none      ; the current-call
        curr-base: none      ; the current knowledge base
        curr-first: true     ; A flag to determine if it's the first call (used only for trace)

        state: [             ; the list of properties that represent the state of the call and to save in the stack
            save-vars
            curr-goal
            curr-goals
            curr-vars
            curr-clauses
            curr-call
            curr-base
        ]
        stack: make block! 500 ; the stack to save the states of the call
    ]

; Set of internal predicates.
;
; As said somewere else, nothing except CUT and FAIL is hardcoded
;
; These internal clauses are standards clauses
; ****************************************************************

    internal: does [internal: assert none [

; NOT
        not [X Y] [
            X Y ! fail
        ]
        not [_ _] [!]
; EQUAL?
        equal? [X X] [!]

; NOT-EQUAL?
        not-equal? [X X] [
            ! fail
        ]
        not-equal? [_ _] [!]
; IF
        if [X] [
            equal? [false (not X)] !
        ]
; FREE
        free [X] [
            equal? [true (none? X)] !
        ]
; BOUND
        bound [X] [
            equal? [false (none? X)] !
        ]
; ADD
        add [X Y (X + Y)][!]
        add [X (Z - X) Z][!]
        add [(Z - Y) Y Z][!]
; MULT
        mult [X Y (X * Y)][!]
        mult [X (Z / X) Z][!]
        mult [(Z / Y) Y Z][!]
; REPEAT
        repeat []
        repeat [] [
            repeat []
        ]

        repeat [1] [!]
        repeat [X] [
            if [(X > 0)]
        ]
        repeat [X] [
            if [(X > 0)]
            repeat [(X - 1)]
        ]
    ]]

; This function determine if a terme is a local var
; *************************************************

    clause-var?: func [
        X
        /local p
    ][
        all [
            not equal? '_ X
            word? X
            any [
                equal? "_" p: copy/part to-string X 1
                not strict-equal? p lowercase copy p
            ]
        ]
    ]

; This function return a block with all the local var in a block
; ***************************************************************

    get-clause-vars: func [
        X
        /local result
    ][
        if any [
            block? X
            map? X
            vector? X
        ][
            result: copy []
            foreach item X [
                append result get-clause-vars item
            ]
            return result
        ]
        if all [
            clause-var? X
        ][
            return reduce [X]
        ]
        return copy []
    ]

; This function transform a clause in the internal form
; *****************************************************

    to-clause: func [
        name [word!]
        pattern [block!]
        goals [block!]
        /local vars result
    ][
        result: compose/only [
            predicat: (compose/only [(name) (pattern)])
            goals: (goals)
            vars: (vars: union get-clause-vars pattern get-clause-vars goals)
        ]
        foreach item vars [
            append result compose [(to-set-word item)]
        ]
        if not empty? vars [append result [none]]
        result
    ]

; Append a clause to the knowledge base
; *************************************

    append-clause: func [
        base [block!]
        name [word!]
        pattern [block!]
        goals [block!]
        /local clauses
    ][
        if not clauses: select base name [
            append base compose/only [(name) (clauses: copy [])]
        ]
        append/only  clauses to-clause name pattern goals
    ]

; This function remove a clause from the knowledge base
; *****************************************************

    remove-clause: func [
        base [block!]
        predicat [block!]
        flag [none! logic!]
        /local save object result
    ][
        local: copy []
        save: copy []
        result: false
        local: get-clause-vars predicat
        foreach item local [
            append save either value? item [
                get item
            ][
                none
            ]
        ]
        while [not empty? base] [
            set local save
            object: make clause first base
            either unify predicat object/predicat [
                base: remove base
                result: true
                if not flag [
                    break
                ]
            ][
                base: skip base 1
            ]
        ]
        set local save
        result
    ]

; *************************************************************************************
; Unification of two termes function
; **********************************
; - unification is in the same time assignation and comparaison
; - the main idea is that if two terme are assigned, we compare them
;   otherwise in case of vars, the unbound terme is assigned to the value of the other.
; - in case of block, each element is unified
; - the | indicates that the reste of the other block
;   must be unified with the following terme
; - in case of parenthesis, the code within is executed
; - for the anonym vars _, the unification always occurs
; - the function stop as soon as the unification fails
; *************************************************************************************


; -----------------------------------------------------------------------------------------------------------------------------------------
; Performance consideration
; -------------------------
; In the first version I used a lot of recursive call of unify
; because it was easier to write the logic but I transform it
; into loop (mainly while) because it's faster (even if it's
; harder to understand and maintain the logic)
; -----------------------------------------------------------------------------------------------------------------------------------------

    unify: func [
        X [block! map! vector!]
        Y [block! map! vector!]
        /local V TX TY VX VY p q pX pY
    ][

; ************************************
; We loop on each elements of the list
; ************************************

        while [on] [

if unify-trace [
    print "Unification"
    probe X
    probe Y
]

; =====================
; If two blocks are :
; - different length
; - and without |
; the unification fails
; =====================

        if not any [
            equal? length? X  length? Y
            find X '|
            find Y '|
        ][
if unify-trace [print "Case 1 --> Unification FAIL"]
            return false
        ]

; ========================
; If two block are :
; - the same
; - without speciality ;-)
; unification occurs
; ========================

        if all [
            equal? X Y
            not any [
                find-special X
                find-special Y
            ]
        ][
if unify-trace [print "Case 2 --> unification OK"]
            return true
        ]

; ====================================
; This is the case when a terme is a |
; ====================================

            if equal? '| pick X 1 [
                either block-term? VX: get-term TX: pick X 2 [
if unify-trace [print "Case 3.X.1"]
                    change/part X VX 2
                ][
                    if all [
                        none? VX
                        var-term? TX
                    ][
                        VX: TX
                    ]
                    VX: compose/only [(VX)]
                    VY: compose/only [(Y)]
                    either unify VX VY [
if unify-trace [print "Case 3.X.2"]
                        return true
                    ][
if unify-trace [print "Case 3.X.3"]
                        return false
                    ]
                ]
            ]

            if equal? '| pick Y 1 [
                either block-term? VY: get-term TY: pick Y 2 [
if unify-trace [print "Case 3.Y.1"]
                    change/part Y VY 2
                ][
                    if all [
                        none? VY
                        var-term? TY
                    ][
                        VY: TY
                    ]
                    VX: compose/only [(X)]
                    VY: compose/only [(VY)]
                    either unify VX VY [
if unify-trace [print "Case 3.Y.2"]
                        return true
                    ][
if unify-trace [print "Case 3.Y.2"]
                        return false
                    ]
                ]
            ]

; =============================================
; If we are here, one of the two block is empty
; The unification fails
; =============================================

        if any [
            empty? X
            empty? Y
        ][
if unify-trace [print "Case 4 --> unification FAIL"]
            return false
        ]

; ================================================
; Here we consider the Y terme (TY)
; and for each case, we considere the X teme (TX)
; ================================================

            VX: get-term TX: pick X 1
            VY: get-term TY: pick Y 1
            either none? VX [
                if var-term? TX [
                    either none? VY [
                        if var-term? TY [
if unify-trace [print "Case 5.1"]
                            set TX TY
                        ]
if unify-trace [print "Case 5.2"]
                    ][
if unify-trace [print "Case 5.3"]
                        set TX VY
                    ]
                ]
if unify-trace [print "Case 5.4"]
            ][
                either none? VY [
                    if var-term? TY [
if unify-trace [print "Case 5.5"]
                        set TY VX
                    ]
if unify-trace [print "Case 5.6"]
                ][
                    either all [
                        block-term? VX
                        block-term? VY
                    ][
                        if not unify VX VY [
if unify-trace [print "Case 5.7"]
                            return false
                        ]
if unify-trace [print "Case 5.8"]
                    ][
                        if not equal? VX VY [
if unify-trace [print "Case 5.9"]
                            return false
                        ]
if unify-trace [print "Case 5.10"]
                    ]
                ]
            ]

; ==============================
; Here we loop to the next terme
; ==============================

            x: next X
            Y: next Y
        ]
    ]

; ****************************************************
; This function get the value of a term (can be a var)
; ****************************************************

    get-term: func [
        X
        /deep
        /local p q r
    ][
        x: get-var X
        if all [
            paren? X
            not error? p: try to-block X
        ][
            X: p
        ]
        if equal? '_ X [
            x: none
        ]
        if all [
            deep
            block-term? X
        ][
            X: get-block X
        ]
        X
    ]

; ************************************
; This function get the value of a var
; ************************************

    get-var: func [
        X
    ][
        while [
            var-term? X
        ][
            X: get X
        ]
        X
    ]

; ***************************************************
; This function remove as much as possible in a block
; ***************************************************

    get-block: func [
        X [block! map! vector!]
        /local p q r block-rule
    ][

        block-rule: [any [p: 
        (p: find-special2 p)
        :p [

            p: '_ 
            (change/only p none) :p
        |
            p: '| set q [block! | map! | vector!]
            (change/part p q 2) :p
        |
            p: '| set q word!
            (either all [
                var-term? q
                block-term? q: get-term q
            ][
                change/part p q 2
            ][
                p: skip p 2
            ]) :p
        |
            p: set q paren!
            (either not error? q: try to-block q [
                change/only p q
            ][
                p: next p
            ]) :p
        |
            p: set q word!
            (either all [
                var-term? q
                not none? q: get-term q
            ][
                change/only p q
            ][
                p: next p
            ]) :p
        |
            set q [block! | map! | vector!]
            (parse q block-rule)
        | 
            skip
        ]]]

        parse X block-rule
        X
    ]


; ***********************************************
; This function determine if the terme is special
; ***********************************************

    special-rule: [
        [to none! | to '_ | to word! | to paren! | to block! | to map! | to vector!]
        to end
    ]
    find-special: func [
        X [block! map! vector!]
    ][
        parse x special-rule
    ]


; ******************************************
; This function find the first special terme
; ******************************************

    find-special2: func [
        X [block! map! vector!]
        /local p q r
    ][
        q: index? tail p: X
        parse X [
            [to '_ r: (q: minimum q index? r) | none] :p
            [to '| r: (q: minimum q index? r) | none] :p
            [to word! r: (q: minimum q index? r) | none] :p
            [to block! r: (q: minimum q index? r) | none] :p
            [to map! r: (q: minimum q index? r) | none] :p
            [to vector! r: (q: minimum q index? r) | none] :p
        ]
        at head X q
    ]


; *******************************************
; This function determine if a terme is a var
; *******************************************

    var-term?: func [X][
        all [
            not equal? '_ X
            word? X
            value? X
            not any-function? get X
        ]
    ]

; ************************************************************************
; This function determine if the terme is a list for the engine (a block?)
; ************************************************************************

    block-term?: func [
        X
    ][
        find reduce [block! map! vector!] type? X
    ]

; **************************************************************************************
; Here we have logic that does the call of sub-goal, the matching and backward chaining
;
; The main idea for backward chaining is to keep the state of the call within an object
; and to stack the sate of the object in a block, so the state of the object
; can be restore when a backward chaining si done.
;
; The main functions are :
; - goal            which is a public function allowing the call of goal
; - for-which       which is also a public function allowing call of goal
; - call?           which contain the logic to call every sub-goal of a goal,
;                   and does backward chaining
; - next-goal       which calculates the next goal to call,
;                   clear the stack when a cut (|) is found
;                   and process the code placed within parenthesis
; - match-clauses   that extract clauses that match the current processed sub-goal
;
; Other function are defined here :
; - bench-goal      which is a bench helper
; - free-call       that free that set to none all the properties of a call object
; - append-match    which is used by match-clauses
; - to-vars-block   which is use by for-which
; - remove-clause   which is used when a cut (|) is found to remove 
;                   the current clause in the parent call object
; **************************************************************************************

; -----------------------------------------------------------------------------------------------------------------------------------------
; Performance consideration
; -------------------------
; - All the methods are outside the object because the logic can do a lot of make
;   of the object that store the state of the call.
; - I notice that to make an object with many method (function)
;   is slower than an object with few method
; - But I also notice that using path to get the properties of object
;   is also longer than accessing these properties a method of the object
; - In the call? function I also try to use "use" function 
;   (use bind/copy o in o 'self [......]) to avoid the use of path but it doesn't work.
; - "reduce" or "set" work well with "bind/copy o in o 'self" but "use" doesn't.
; - So I don't know what is the best, slow make and fast method or fast make
;   and slow function. The best would be fast-fast solution
;
; - For the stack, I insert and remove data at the head of the block.
; - I do not find better performance to append data at the end of the stack
; - I tried to use list but the behavior of function on list is not the same
;   as block so I didn't go further in this way.
;
; -----------------------------------------------------------------------------------------------------------------------------------------


; *****************************
; Function which execute a goal
; *****************************

    set 'goal func [
        "Try a goal and return the number of solution"
        base [block!] "The KB to use"
        goals [block!] "The goals to try"
        /local curr-call i
    ][
        curr-call: make clause to-clause 'goal [] goals
        i: 0
        while [call? curr-call base none] [i: i + 1]
        i
    ]

; *****************************************************************
; Function that execute a block of code for each solution of a goal
; *****************************************************************

    set 'for-which func [
        [throw]
        base [block!] "The KB to use"
        'word [word! block!] "The word or block of word to set for each solutions (will be local)"
        goals [block!] "The goals to try"
        body [block!] "The block to evaluates for each solutions"
        /local curr-call
    ][
        word: to-vars-block word
        curr-call: make clause to-clause 'for-which word goals
        do compose/only/deep [
            use (word) [
                while [call? curr-call base none] (compose/deep [
                    set [(word)] reduce second curr-call/predicat
                    (body)
                ])
            ]
        ]
    ]

; *********************************
; Function which help to do a bench
; *********************************

    set 'bench-goal func [
        "Try a goal and return the number of solution"
        count [integer!]
        base [block!] "The KB to use"
        goals [block!] "The goals to try"
        /local curr-call curr-clause
    ][
        curr-clause: to-clause 'bench [] goals
        bench count [
            curr-call: make clause curr-clause
            while [call? curr-call base none] []
        ]
    ]

; ***************************************************************************************
; Function that call a goal
; - This is the main logic of the inference engine
; - It find the next goal to call, match the goal in the knowledge base, and call the sub goal
; - It's one of the most difficult logic of the script
; - This function is re-called while true is returned (to find all possible solutions)
; - What is done :
;   - if it's the first call :
;     - initialize the call object
;     - determine the next sub-goal
;     - when the first sub-goal is fail, return false (the goal is not satisfied)
;     - if there no sub-goal, return true (it's a fact and the goal is stisfied)
;   - if it's not the first call :
;     - if the curr-goal is empty, return false (it's the second call of a fact)
;   - after this initialization, a loop is done while the sub-goal list is not empty
;     - if there is a call to do :
;       - restore the variables of the call object
;       - call the goal solved hre
;       - resolve the variables (some are not solved during unification so they are solved here)
;       - determine the next goal
;       - if the call is successfull and also the next-goal function doesn't find a fail
;         - if the sub-goal list is empty, return true (the goal is satisfied)
;       - otherwise, if the current sub-goal is empty
;         - free the call object
;         - return false (the goal fail)
;     - if there is no current-call, determine the next call to do
;       - restore the current sucb-goal
;       - restore the current variables
;       - loop while the clauses list is not empty
;         - make a new call object bound with the current call
;         - try to unify the current sub-goal with the head of the call
;         - if unificytion is OK, save the varables and break the loop
;         - otherwise, restore the current sub-goal, the current variable and loop to the next clause
;     - if there is still no call to do afeter the unification
;       - if the stack is empty :
;         - free the current call
;         - return false (the goal is not satisfied)
;       - if the stack is not empty,
;         - pull the previous state (backward chaining) and loop
; ***************************************************************************************

    call?: func [
        o [object!]
        base [block!]
        parent-clauses [block! none!]
        /local curr-goal X p q
    ][

; ================================================================================
; If the list of current sub-goal is none it's the first call
; (the call object is not initialized)
; - initialize the call object
; - determine the next sub-goal
; - if a fail is encountered, return false (the goal is not satisfied)
; - if the next goal is empty, return true (it's a fact)
; Otherwise, it's a second, third, etc... call :
; - if the current su-goal is empty, return false (it's the second call of a fact)
; - otherwise, continue the processing.
; ================================================================================

        either none? o/curr-goals [
            o/curr-goal: copy []
            o/curr-goals: copy o/goals
            o/curr-vars: copy/deep reduce o/vars
            o/curr-clauses: copy []
            o/curr-call: none
            o/curr-first: true
            o/curr-base: base
            o/save-predicat: copy/deep o/predicat
            o/save-vars: copy/deep o/curr-vars
            if call-trace [
                print ["CALL" mold/only get-block copy/deep o/predicat]
            ]
            curr-goal: next-goal o base parent-clauses
            if not curr-goal [
                if call-trace [
                    print ["NO solution"]
                ]
                free-call o
                return false
            ]
            if empty? curr-goal [
                if call-trace [
                    print ["RETURN 1" mold/only get-block copy/deep o/predicat]
                ]
                return true
            ]
        ][
            if empty? o/curr-goal [
                return false
            ]
            o/predicat: copy/deep o/save-predicat
            if call-trace [
                print ["REDO" mold/only o/predicat]
                o/curr-first: false
            ]
        ]

; ================================================
; Main loop (while there is a sub-goal to process)
; ================================================

        while [not empty? o/curr-goals][

; --------------------------------------------------------------------------
; If there is a call to do :
; - restore the vars value
; - Call the sub-goal
; - resolve the variables (if the call is successfull)
; - determine the next sub-goal to do
; - if the call and naxt-goal are successfull :
;   - if the next sub-goal is empty (there is no more sub-goal to do)
;     - return true (the goal is satisfied)
; - otherwise
;   - if the next sub-goal is empty (only when the last subgoal is a fail) :
;     - free the call object
;     - return false (the goal is not satisfied)
; --------------------------------------------------------------------------

            if o/curr-call [
                set o/vars copy/deep o/save-vars
                either if call? o/curr-call o/curr-base o/curr-clauses [
                    foreach p o/vars [
                        if not none? q: get-term/deep p [
                            set p q
                        ]
                    ]
                    curr-goal: next-goal o base parent-clauses
                    
                ][
                    if empty? curr-goal [
                        if call-trace [
                            print ["RETURN 2" mold/only get-block copy/deep o/predicat]
                        ]
                        return true
                    ]
                ][
                    if empty? o/curr-goal [
                        if call-trace [either o/curr-first [
                            print ["NO solution"]
                        ][
                            print ["NO MORE solution"]
                        ]]
                        free-call o
                        return false
                    ]
                ]
            ]

; ------------------------------------------------------------------------------
; Determine the next call to do
; - restore the sub-goal
; - restore the vars value
; - loop while the clauses block (determined by next-goal function) is not empty
;   - make the call object
;   - if the unification is successfull :
;     - save the vars value
;     - break the loop
;   - otherwise :
;     - restore the sub-goal (because the unification can change
;       it even if the unification fail)
;     - restore the vars value (because the unification can change
;       it even if the unification fail)
;     - and loop
; ------------------------------------------------------------------------------

            o/curr-call: none
            curr-goal: copy/deep o/curr-goal
            set o/vars copy/deep o/curr-vars
            while [not empty? o/curr-clauses][
                o/curr-call: make clause bind/copy first o/curr-clauses o ;in o 'self
                o/curr-clauses: next o/curr-clauses
                if unify curr-goal o/curr-call/predicat [
                    o/save-vars: copy/deep reduce o/vars
                    break
                ]
                o/curr-call: none
                curr-goal: copy/deep o/curr-goal
                set o/vars copy/deep o/curr-vars
            ]

; ---------------------------------------------------------------
; If there is no call to do (backward chaining)
; - if the stack is empty (all possible backward are done) :
;   - free the object
;   - return false (the goal is not satisfied) 
; - otherwise
;   - pull the data from the stack
; ---------------------------------------------------------------

            if none? o/curr-call [
                if empty? o/stack [
                    if call-trace [either o/curr-first [
                        print ["NO solution for" mold/only o/predicat]
                    ][
                        print ["NO MORE solution for" mold/only o/predicat]
                    ]]
                    free-call o
                    return false
                ]
                set o/state o/stack
                set o/vars copy/deep o/curr-vars
                remove/part o/stack length? o/state
            ]
; --------------
; En of the loop
; --------------
        ]

; --------------------------------------------
; Here, we are at the end of the sub-goal list
; There is no more solution for the goal, so :
; - we free the object
; - we return false
; --------------------------------------------

        if call-trace [either o/curr-first [
            print ["NO solution"]
        ][
            print ["NO MORE solution"]
        ]]
        free-call o
        return false
    ]

; *************************************************
; This function free all the pointers in the object
; *************************************************

    free-call: func [
        o [object!]
    ][
            o/save-predicat: none
            o/save-vars: none
            o/curr-goal: none
            o/curr-goals: none
            o/curr-vars: none
            o/curr-clauses: none
            o/curr-call: none
            o/curr-first: none
            o/curr-base: none
            o/state: none
            o/stack: none
    ]

; **********************************************************************
; Determine the next goal to process
; - loop on the sub-goal list
; - get the next sub-goal
; - if the next sub-goal is empty
;   - return because we are at the end of the sub-goal list
; - if the next sub-goal is a FAIL
;   - returne none beacause the goal is not achieved
; - if it's a CUT (!)
;   - remove the goal from the parent clauses
;   - empty the stack
;   - re-initialize the stack
; - if it's a parenthesis (the code within is executed)
;   - if we are at the head of the list
;     - we remove the parenthesis to avoid multiple exection of the code
;       during backward chaining
;   - and we execute the code
; - otherwise, it's a standard goal
;   - if it's a path, the first part gives the base tu use
;   - we take also the parameters of the goal
;   - and we call th function that match the sub-goal in the base
;   - we save the current state un the stack
;   - we intitialize the object with the new state
;   - and we return the goal
; **********************************************************************

    next-goal: func [
        o [object!]
        base [block!]
        parent-clauses [block! none!]
        /local p goal goals clauses
    ][
        goal: o/curr-goal
        goals: o/curr-goals
        while [on] [
            goals: skip goals length? goal
            if empty? goal: copy/part goals 1 [
                return goal
            ]
            if equal? [FAIL] goal [
                return none
            ]
            if not any [
                if any [
                    equal? [CUT] goal
                    equal? [!] goal
                ][
                    if parent-clauses [
                        remove-clauses parent-clauses o/predicat
                    ]
                    clear o/stack
                    o/save-vars: none
                    o/curr-goal: goal: copy []
                    o/curr-goals: goals: skip goals 1
                    o/curr-vars: copy/deep reduce o/vars
                    o/curr-clauses: copy []
                    o/curr-call: none
                    o/curr-base: base
                    true
                ]
                if paren? first goal [
                    if head? goals [
                        remove goals
                        remove o/curr-goals
                    ]
                    do goal
                    true
                ]
            ][
                if path? p: get-term/deep first goal [
                    base: get first p
                    change goal second p
                ]
                append/only goal second goals
                if empty? clauses: match-clauses goal base [
                    return false
                ]
                insert o/stack reduce o/state
                o/save-vars: none
                o/curr-goal: copy/deep goal
                o/curr-goals: goals
                o/curr-vars: copy/deep reduce o/vars
                o/curr-clauses: clauses
                o/curr-call: none
                o/curr-first: true
                o/curr-base: base
                return goal
            ]
        ]
    ]

; **************************************************************************
; This function match the goal within the knowledge base
; - if the first term of the goal is a var or _ or none,
;   - the fuction return the entire knowledge base
; - otherwise
;   - call the function append-match that find the sub-goal une th base
;   - if the result is empty
;     - try to find the sub-goal in the internal base (pre-defined clauses)
;   - if the result is still empty and the goal end with a question mark (?)
;     - build automaticaly a clause like xxx? [parms] [xxx [parms] !]
;
; **************************************************************************

    match-clauses: func [
        goal [block!]
        base [block!]
        /local result name p
    ][
        result: copy []
        name: pick goal 1
        if all [
            var-term? name
            p: get name
        ][
            name: p
        ]
        either any [
            find reduce ['_ none] name
            var-term? name
        ][
            foreach [item1 item2] base [
                insert tail result item2
            ]
        ][
            append-match name base result

            if empty? result [
                append-match name internal result
            ]

            if all [
                empty? result
                equal? 'call name
            ][
                p: first reduce compose/only [(pick goal 2)]
                append/only result to-clause
                    'call
                    [| _]
                    p
            ]

            if all [
                empty? result
                equal? #"?" last name: to-string name
            ][
                append/only result to-clause
                    to-word name
                    p: pick goal 2
                    compose/only [(to-word copy/part name subtract length? name 1) (p) !]
            ]
        ]
        goal: base: p: none
        result
    ]

; *************************************************************
; This function allow to add the corresponding clause to a goal
; *************************************************************

    append-match: func [
        name [word!]
        base [block!]
        result [block!]
    ][
        while [not none? base: find/skip base name 2][
            insert tail result pick base 2
            base: skip base 2
        ]
        base: result: none
    ]

; ***************************************
; This function tansform all word in vars
; ***************************************

    to-vars-block: func [
        word [word! block!]
        /local X
    ][
        if word? word [word: to-block word]
        forall word [
            X: to-string to-word first word
            change X to-char uppercase to-string first X 
            change word to-word X 
        ]
        head word
    ]

; *******************************************************
; This function erase the clauses corresponding to a goal
; *******************************************************

    remove-clauses: func [
        clauses [block!]
        goal [block!]
    ][
        forall clauses [
            if equal? first goal first second first clauses [
                remove clauses
            ]
        ]
        exit
    ]

; ***************************************
; This function allows to execute a block
; within the context of an object
; ***************************************
    with: func [
        [throw]
        object [object!]
        body [block!]
    ][
        do bind/copy body in object 'self
    ]

; **************************************
; This function allows to do a benchmark
; **************************************

    bench: func [
        "Return the elapse time to evaluates a block a specified number of times."
        count [integer!] "Number of repetitions"
        block [block!] "Block to evaluate"
        /local t1 t2 t3
    ][
        t1: now/time/precise
        loop count []
        t2: now/time/precise
        loop count block
        t3: now/time/precise
        (t3 - t2) - (t2 - t1)
    ]

; ***************************************************
; This function incerments an elapsed time "compteur"
; ***************************************************

    bench-time: func [
        "Return the elapse time to evaluates a block a specified number of times."
        'time [word!] "The word to increment with the elapse time"
        block [block!] "Block to evaluate"
        /local t1 t2 result
    ][
        t1: now/time/precise
        set/any 'result do block
        t2: now/time/precise
        set time add (t2 - t1) get time
        either value? 'result [
            return result
        ][
            exit
        ]
    ]
; **********************
; * DIAGNOSTIC engine *
; **********************
;
; This engine allows you to ...
;
; ***************************************************************************
    set 'diagnostic func [
        "Run a diagnostic knowledge database"
         Knowledge [block!] "Knowledge base"
         Fact [block!] "Fact base (cleared on each run)"
    ][
        clear fact
        until [
            goal knowledge [
                deduction [X Y]
                call X
                (assert fact compose/deep Y)
           ]
           zero? goal knowledge [
               query [X Y Z]
                call X
                (inform layout compose [ (Y) across return btn-enter [
                    assert fact compose/deep Z hide-popup
                ]])
            ]
        ]
        goal knowledge [
            conclusion []
        ]
    ]
]
