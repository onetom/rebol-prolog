REBOL[]
    do %prolog.r
    print ""
    print "****************************"
    print "**** Start of benchmark ****"
    ex-base: assert none probe [
        concat [[] L L] [!]
        concat [[X | L1] L2 [X | L3]] [
            concat [L1 L2 L3]
        ]
        nrev [[] []] [!]
        nrev [[X | Y] L] [
            nrev [Y Z]
            concat [Z [X] L]
        ]
    ]
    i: 100
    j: 0
    t: bench-goal i ex-base [
        nrev [[1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30] L]
        (print ["Boucle :" j: j + 1])
    ]

    print ["Length" t]
    print ["Performance (LIPS)" (i * (30 + 1) * (30 + 2) / 2) / to-decimal t]

    print ""
    print "**** End of benchmark ****"
    print "**************************"
