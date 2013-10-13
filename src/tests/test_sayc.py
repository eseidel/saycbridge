# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

# FIXME: This doesn't need to be in python anymore, and could just be a text file?
sayc_expectations = {
    "test_open_one_nt": [
        ["KQ4.AQ8.K9873.K2", "1N"],  #p2
        ["97.KJ2.AT3.AKQ95", "1N"],  #p2
        ["AQJ97.53.KQ2.A65", "1N"],  #p3, h1
        ["AQJ.J2.Q9832.AK5", "1N"],  #p3, h2
        ["T74.QT8.AKQ86.A5", "1N"],  #p3, h3
        ["AJ763.Q32.K8.A65", "1C"],  #p3, h4
        ["AKT92.T98.AQ9.AT", "1N"],  #p3, h5 - Too "big", plan to do 1C, 2N
    ],

    "test_open_two_nt": [
        ["KQ4.AQ8.AK873.K2", "2N"],
    ],

    "test_weak_game_jump_over_one_nt": [
        # FIXME: The book says to "get your partnership to game" with h1.  Probably easiest with a texas transfer.
        # Treating this like h21 (p11), expecting a transfer then jump to game.
        ["K74.9.J98.KJT742", "4S", "1N P 2H P 2S P"],  # p6, h1
        ["Q87.J843.K65.Q93", "P", "1N P"],  # p6, h2
    ],

    "test_minimum_stayman": [
        ["T9.AJ72.K65.Q732", "X", "1N 2C"],
        ["T9.AJ72.K65.Q732", "3N", "1N P 2C P 2D P"],  # p6, h3
        ["T9.AJ72.K65.Q732", "3N", "1N P 2C P 2H P"],  # p6, h3
        ["T9.AJ72.K65.Q732", "4S", "1N P 2C P 2S P"],  # p6, h3
        ["T2.AJ7.J652.QJ32", "2N", "1N P 2C P 2D P"],  # p6, h4
        ["T2.AJ7.J652.QJ32", "3H", "1N P 2C P 2H P"],  # p6, h4
        ["T2.AJ7.J652.QJ32", "3S", "1N P 2C P 2S P"],  # p6, h4
        ["T9.AJ72.Q732.K65", "3N", "1N P 2C P 2D P"],  # p6, h5
        ["T9.AJ72.Q732.K65", "4H", "1N P 2C P 2H P"],  # p6, h5
        ["T9.AJ72.Q732.K65", "3N", "1N P 2C P 2S P"],  # p6, h5

        # Sanity check that partner knows how to respond with no major:
        ["AQ2.AJ72.Q73.K65", "2D", "1N P 2C P"],
    ],

    "test_invitational_stayman": [
        ["T9.AJ.K652.QT732", "3S", "1N P 2C P 2D P"],  # p7, h6
        ["T9.AJ.K652.QT732", "4H", "1N P 2C P 2H P"],  # p7, h6
        ["T9.AJ.K652.QT732", "4S", "1N P 2C P 2S P"],  # p7, h6
        ["832.A.QJ652.JT73", "2H", "1N P 2C P 2D P"],  # p7, h7
        ["82.A7.QJ652.KT73", "3H", "1N P 2C P 2D P"],  # p7, h8
    ],

    "test_3c_stayman": [
        ["T9.AJ2.T652.T973", "3C", "2N P"],
        ["AQ.AQ2.AK52.Q973", "3H", "2N P 3C P"],
        ["T.AJ2.T652.T9739", "X", "2N 3C"], # Stolen stayman works too (and also prefers stolen stayman over a transfer with 4-5)
        ['Q.T43.JT92.KT863', '4H', 'P 2N P 3C P 3H P'],  # 14-59d6f2b05f85e1f680b938c4a3, N, 3C is never garbage stayman.
    ],

    "test_escape_route_stayman": [
        ["9.8753.7652.8732", "P", "1N P 2C P 2D P"],  # p8, h9
        ["9.8753.7652.8732", "P", "1N P 2C P 2H P"],  # p8, h9
        ["9.8753.7652.8732", "P", "1N P 2C P 2S P"],  # p8, h9
        ["2.J8742.652.Q732", "P", "1N P 2C P 2D P"],  # p8, h10
        ["2.J8742.652.Q732", "P", "1N P 2C P 2H P"],  # p8, h10
        ["2.J8742.652.Q732", "P", "1N P 2C P 2S P"],  # p8, h10
        ["8.T9762.Q732.J65", "P", "1N P 2C P 2D P"],  # p8, h11
        ["8.T9762.Q732.J65", "P", "1N P 2C P 2H P"],  # p8, h11
        ["8.T9762.Q732.J65", "P", "1N P 2C P 2S P"],  # p8, h11
    ],

    "test_jacoby_transfers": [
        # Basic Jacoby Transfers
        ["J83.T.QT8432.Q65", "P", "1N P 2D P 2H P"],  # p9, h12
        ["983.7.T843.KQ765", "P", "1N P 2H P 2S P"],  # p9, h13
        ["83.8.KT843.97652", "P", "1N P 2D P 2H P"],  # h14, p9
        # Skipped hand 15, since it's covered later.
        # Jacoby with invitational hands
        ["J9.532.K32.KJ865", "2N", "1N P 2H P 2S P"],  # h16, p10
        ["9.32.KJ832.QJ765", "2S", "1N P 2D P 2H P"],  # h17, p10
        ["J97.Q2.KJ9832.65", "3H", "1N P 2D P 2H P"],  # h18, p10
        # Jacoby with game-force hands
        ["A9.532.K32.KJ865", "3N", "1N P 2H P 2S P"],  # h19, p11
        # FIXME: It's unclear if h20 should have slam interest (thus 3H instead of 4H).
        ["A.32.KJ832.QT765", "4H", "1N P 2H P 2S P"],  # h20, p11

        # FIXME: This sequence is awkward and likely to confuse many partners.
        ["A.32.AKJ82.QT765", "3H", "1N P 2H P 2S P"],  # 29-31 combined hcp. Looks slammy.

        ["A.3.KJ8532.JT764", "4H", "1N P 2D P 2H P"],  # With 6-5 and weak, no need to explore spades?

        # FIXME: h21 could also be bid with Texas transfers (because it has no slam interest).
        ["97.A2.KJ9832.J76", "4H", "1N P 2D P 2H P"],  # h21, p11
        ["97.AQ982.2.KJT76", "3D", "1N P 2H P 2S P"],  # h22, p11
        ["AQ982.97.2.KJT76", "3C", "1N P 2H P 2S P"],  # corollary to h22
        # Jacoby jump raise with 4c trump support.
        ["A9.AQ5.AQT4.J865", "3H", "1N P 2D P"], # p12
        # Jacoby with long weak minors
        ["JT98765.2.75.543", "P", "1N P 2S P 3C P"], # p12, h23
        ["5.QT87542.75.543", "3D", "1N P 2S P 3C P"], # p12, h24

        # Sanity-check that partner knows how to accept.
        ["97.KJ52.AT3.AKQ9", "3C", "1N P 2S P"],

        # Transfers are on over higher level NT as well:
        ['K83.852.5.QT9752', '3H', '2N P', 'Both'],  # 4-1bc6c9d271a2f39a0ef106751b, E
        ['83.852.5.KQT9752', '4H', '2C P 2D P 3N P'],
        ['K83.852.QT9752.5', '3D', '2N P', 'Both'],  # 4-1bc6c9d271a2f39a0ef106751b, E
        ['83.852.KQT9752.5', '4D', '2C P 2D P 3N P'],

        # Needs SpadesRebidAfterHeartsTransfer defined for higher-level transfers to not be None:
        ['972.T872.97653.J', 'P', 'P 2C P 2D P 2N P 3D P 3H P', 'Both'],  # 10-19847dc6f0cba48049a7f75f2a, N

        # What about super-accepts?  Even if partner only has 6hcp, we want to go to game!
        ['KQT.AK763.AK6.84', '4H', 'P 1D P 1H P 2N P 3D P'],  # 1-0ba065f416fa5fc432d61c9af2, E
    ],

    "test_invitational_two_nt_over_one_nt": [
        ["QT987.AJ4.75.J43", "2N", "1N P"],  # p13, h25
        ["T732.KJ95.J32.A5", "2N", "1N P"],  # p13, h26
        ["952.QT87.A86.Q52", "P", "1N P"],  # p13, h27

        # With only 6 points, game is remote.  Pass.
        ['K8732.J98.J5.JT8', 'P', 'P P 1N P', 'N-S'],  # 12-f87c17a2a7cc6139a714067be4, W
    ],

    "test_three_level_calls_over_one_nt": [
        ["AQT942.984.75.43", "3C", "1N P"],  # p13, h28
        ["8.KQ98752.86.542", "3D", "1N P"],  # p13, h29
        ["8.AK98752.86.542", "3N", "1N P"],  # p13, h30
    ],

    "test_slam_invitations_over_one_nt": [
        # Major slam invitational responses over 1N
        ["K7.J85.A2.KQJ743", "3S", "1N P"],  # p14, h31
        ["KQ9.5.KQT652.AT8", "3H", "1N P"],  # p14, h32

        # Minor slam invitational sequences over 1N
        ["AK8743.K2.K52.J8", "3C", "1N P 2C P 2H P"],  # p14, h33
        ["A3.KJT976.KQ2.76", "3D", "1N P 2C P 2H P"],  # p14, h34

        # Doesn't seem that slammy and should just jump to 4S?
        ['Q43.A7642..AQJ32', '4S', '1N P 2C P 2S P', 'N-S'],  # 5-287fd9266bc32547d472b40fa2, S

        # Gerber over 1NT (these hands are generated by me) (p14)
        ["KQ4.KQJ.K9873.K2", "5D", "1N P 4C P 4D P 5C P"],
        ["KQ4.AQ8.K9873.K2", "5N", "1N P 4C P 4H P 5C P"],
        ["97.KJ2.AT3.AKQ95", "5S", "1N P 4C P 4S P 5C P"],
        ["972.A2.AT3.AKQ95", "5H", "1N P 4C P 4N P 5C P"],
        ["A975.A73.A52.A65", "5D", "1N P 4C P 4D P 5C P"],

        # 4N response to 1N (15hcp = pass, 16hcp = 5N, 17hcp = 6N), p15
        ["AJ4.KQ8.K9873.Q2", "P", "1N P 4N P"],
        ["AJ4.KQ8.K9873.K2", "5N", "1N P 4N P"],
        ["AJ4.KQ8.K9873.A2", "6N", "1N P 4N P"],
    ],

    "test_interference_over_one_nt": [
        # Handling interference (in a NT auction)
        # Using redouble to escape to a minor:
        ["987654.632.5.543", "P", "1N X XX P 2C P"],  # p16, h35
        ["982.T75432.86.32", "2D", "1N X XX P 2C P"],  # p16, h36

        # Sanity check that partner knows how to accept transfer:
        ["AQT.KJ87.J5.KQ43", "2C", "1N X XX P"],

        # When stayman is doubled:
        ["AQT.KJ87.J5.KQ43", "2S", "1N P 2C X"],  # p17, h37
        ["KT82.AKT8.Q8.A62", "P", "1N P 2C X"],  # p17, h38
        ["AKT82.AKT.Q8.862", "XX", "1N P 2C X"],  # p17, h39
        # When Stayman is overcalled:
        ["AQT9.KJ8.J5.KQ43", "2S", "1N P 2C 2H"],  # p18, h40
        ["KT8.AKT8.AQT8.62", "X", "1N P 2C 2H"],  # p18, h41
        ["KT8.AKT8.Q83.A62", "P", "1N P 2C 2H"],  # p18, h42

        # Stolen Stayman response works at the 3-level too:
        ["KT8.AKT8.AQT8.A2", "X", "2N P 3C 3H"],
        ["KT8.AKT8.A2.AQT8", "X", "2N P 3C 3S"],

        # If a transfer is doubled:
        ["AQT.KJ8.AK987.43", "XX", "1N P 2H X"],  # p18, h43
        ["K87.AKT8.AT8.Q62", "2S", "1N P 2H X"],  # p18, h44
        ["AKT.AKJT.87.QT76", "3S", "1N P 2H X"],  # p17, h45
        ["KJ87.AKT8.AT8.62", "P", "1N P 2H X"],  # p17, h46
        # If a transfer is overcalled:
        ["AQT9.KJ87.Q86.A2", "3H", "1N P 2D 2S"],  # p17, h47
        ["KT8.AKT8.86.AQT7", "X", "1N P 2C 2S"],  # p17, h48
        ["KT82.AKT8.Q8.A32", "P", "1N P 2C 2S"],  # p17, 

        # Partner didn't have to transfer, but he did so we should accept it.
        ['A43.KQ.KT942.K54', '2H', '1N X 2D P'],  # 10-d6eab272800d646f171c16bfe4, E

        # Double becomes stayman, and we should only pass for penalties:
        ['J53.AKJ76.A5.Q53', '2D', '1N 2C X P', 'E-W'],  # 16-372932667d6df870144eeda832, W
        # This pass is quesionable?  2C is gonna be hard to set, even with 23 points?
        ['AKJ76.J53.A5.Q53', 'P', '1N 2C X P', 'E-W'],
    ],

    "test_rule_of_twenty_open": [
        # Rule of 20 openings
        ["KT64.6.A873.KQ54", "1C"],  # p26, h1
        ["K953.972..AQJ987", "1S"],  # p26, h2
        ["Q75.Q75.A876.KJ8", "P"],  # p26, h3
        ["7.AKQ8765.Q76.98", "1D"],  # p26, h4
        ["64.6.AK732.QJ854", "1S"],  # p26, h5
        ["KQ953.QJ972.2.A3", "1D"],  # p26, h6
        ["QT83.JT92.A.KQ87", "1D"],  # p27, h7
        ["752.AKQ.QT76.K98", "1C"],  # p27, h8

        # Do I open 1D or 1C?
        ["J73.AQ5.Q83.AJ75", "1C"],  # p27, h9
        ["J8.AQ2.Q873.AJT9", "1D"],  # p27, h10
        ["KQ84.AQ98.QJ8.A4", "1D"],  # p27, h11 # The book says 1C but is contradicting itself.

        # More Rule-of-20
        ["4.Q65.K873.AK975", "1S"],  # p29, h12
        ["AKJ9.T9872.K6.J9", "1D"],  # p29, h13
        ["AK75.9875.AT876.", "1H"],  # p29, h14
        ["K95.AJ765.Q76.J8", "P"],  # p29, h15
    ],

    "test_third_and_fourth_seat_opens": [
        # Third seat openers
        ["AKT9.T87.QJ8.J32", "1C", "P P"],  # p30, h16
        ["KJ3.J8765.9.AJT9", "P", "P P"],  # p30, h17

        # Fourth seat openers
        ["43.765.K83.AQJ75", "1S", "P P P"],  # p32, h15 (ha, she-misnumbered the hands!)
        ["Q98.J972.KJ3.AT9", "P", "P P P"],  # p32, h16
        ["AKT75.K75.T8.742", "P", "P P P"],  # p32, h17

        # Responses are normal after Rule of 15:
        ["3.K8764.AT93.K85", "3S", "P P P 1S P"],
    ],

    "test_minimum_response_to_one_of_a_major": [
        # Skipping h1 and h2 since precise bidding direction is not given.
        ["T64.652.KJ5.A954", "2H", "1H P"],  # p36, h3
        ["9543.K73.T6.A976", "1S", "1H P"],  # p36, h4
        ["KQ975.7532.K7.98", "1N", "1H P"],  # p36, h5
        ["753.97.Q753.K982", "2H", "1H P"],  # p36, h6
        ["753.97.Q753.K982", "2S", "1S P"],  # p36, h6
        ["742.J98.AT874.T6", "1N", "1S P"],  # p36, h7
        ["742.J98.AT874.T6", "4H", "1H P"],  # p36, h7

        # Game is remote with only 5 points.  Pass.
        ['T53.QT93.972.QJ4', 'P', '1H P', 'Both'],  # 7-8c6f19b36d04e1a88e774e6d07, N
    ],

    "test_invitational_response_to_one_of_a_major": [
        # Responding with an invitational hand
        ["432.K765.K8.A753", "1S", "1H P"],  # p36, h8
        ["Q98.KJ732.KJ.JT9", "2D", "1H P"],  # p36, h9

        ["QJ54.J753.KT2.A4", "2C", "1S P"],  # p37, h10
        ["43.KT76.K85.A753", "3H", "1H P"],  # p37, h11

        ["AKJ52.J.J9743.54", "2C", "1H P"], # deal 8791080045553853812852250533176, N underbid by using length points instead of support points
    ],

    "test_game_forcing_resonse_to_one_of_a_major": [
        # Responding with game forcing values or better
        ["K84.AKQ9.76.J984", "1S", "1H P"],  # p38, h12
        ["987.Q732.QJ743.9", "4H", "1H P"],  # p38, h13
        ["42.KJ653.KJ5.KJ7", "2D", "1H P"],  # p38, h14

        ['QJ52.AKQ7.97.KJ2', '3N', '1H P', 'Both'],  # 4-492cd4cb87895e311feda2b247, E
    ],

    "test_jacoby_two_nt_response_to_one_of_a_major": [
        # Jacoby 2N
        ["QJ5.A75.KT8.AT42", "2N", "1S P"],  # p39, h15
        ["87.AQJT9.8.AKJT9", "4D", "1S P 2N P"],  # p40, h16
        # FIXME: The book favors 3H instead of 3S for h17, even though 3S shows 18+ points
        # and slam interest.  Maybe features are higher priority than slam interest?
        ["AQ.Q9763.8.AKQJ8", "3H", "1S P 2N P"],  # p40, h17
        ["J32.K7.KQT83.A75", "4H", "1H P 2N P"],  # p40, h18
        ["2.KJ72.KQT83.A75", "3C", "1H P 2N P"],  # p40, h19
        # FIXME: For h20, the book suggests 3H to show slam interest, even though
        # there are only 19 support points in this hand.
        # Perhaps the support point algorithm is wrong (since it doesn't recognize the 6-card trump support).
        ["AJ2.K7.KQT853.A5", "3H", "1H P 2N P"],  # p40, h20
        ["K3.KJ.KQT83.A754", "3N", "1H P 2N P"],  # p40, h21
        ["8.KQJ72.AJ973.K9", "4D", "1H P 2N P"],  # p40, h22

        # 2o3 is also sufficient for a "strong 5c suit", but is it sufficient to prefer it over 3C?
        ["2.AQ976.98.AKJT8", "4D", "1S P 2N P"],

        # Jacoby2N with only 3 card support seems like our best option.
        ['432.432.AK32.AK2', '2N', '1S P'],
        ['A82.AK8.Q874.T42', '2N', '1S P', 'Both'],  # 10-ca4d11e0a301f6ebe2e7792355, W has no good response.  A 2N "lie" is definitely better than 3N (15-17) or a pass.

        # If we actually have a second suit, we'd rather use that first though?
        ['5432.43.AK32.AK2', '2C', '1S P'],

        ['K.K7.KJ98542.QT8', '2N', '1H P', 'Both'],  # 7-9f9ee86653fd2209088b7f4447, N should bid Jacoby 2NT with 12 hcp?

        # Woe is me, I have 2 singletons and 7 trumps.  Bid the lower singleton first.
        ['K.A743.K.AJ65432', '3C', '1S P 2N P', 'E-W'],  # 3-7fc1123a1b75645f732eaa1c82, 

        # It's not easy having 7 trump and 2 voids.  Slammy?
        ['K.K932.7.AK97653', '3H', 'P 1S P 2N P', 'E-W'],  # 9-c8bb29160f407ae9223e757735, E
    ],

    "test_slam_zone_responses_to_one_of_a_major": [
        # Slam zone bids by responder
        # FIXME:  Need a additional tests to validate a spade raise following jumps in h23, h24
        ["AKJ95.65.KQ3.AKJ", "3C", "1S P"],  # p41, h23
        ["AQ.AKJ76.A32.KQJ", "3D", "1S P"],  # p41, h24 (FIXME: 4NT may also be correct)
    ],

    "test_minimum_response_to_one_of_a_minor": [
        # Responding to one of a minor
        ["T64.652.KJ5.A954", "1S", "1C P"],  # p45, h1
        ["T64.652.KJ5.A954", "1S", "1D P"],  # p45, h1
        ["9532.K72.T86.A97", "1N", "1C P"],  # p45, h2
        ["9532.K72.T86.A97", "1N", "1D P"],  # p45, h2
        ["KQ975.753.K7.987", "2C", "1C P"],  # p45, h3
        ["KQ975.753.K7.987", "1N", "1D P"],  # p45, h3

        ["863.KJ76.T8.K975", "1D", "1C P"],  # p46, h4 (FIXME: 1S may be preferred)
        ["98.KJ752.84.KT95", "1D", "1C P"],  # p46, h5 (FIXME: 1S may be preferred)
        ["42.652.8643.KQJ4", "1H", "1C P"],  # p46, h6

        ["AQ87.AT9.K7.T973", "1S", "1C P 1H P"],  # p47

        # Length points tell us we must mention our hearts.
        ['T8.7.KQT862.9652', '1H', '1C P', 'N-S'],  # 5-14c98344f93dc85b98ae1ad9f3, S

        # Too weak, pass.
        ['954.5.QJT8.J9853', 'P', '1D P', 'Both'],  # 4-85c1fb3f6ca8b02c657077964a, E

        # FIXME: Should we count partner for 4 clubs and support?
        ['5432.KQ2.32.5432', 'P', '1C P'], # Make sure we don't have a hole with 5 hcp and 6 support points.

        # YOLO.  Hope partner doesn't have 3 diamond losers.
        ['AK9842.953.K86.A', '5C', 'P 1C P', 'Both'],  # 7-4725fd646f6238c44adabbb00d, E
    ],

    "test_invitational_response_to_one_of_a_minor": [
        # Responding with invitational hands
        ["43.KJ65.K83.A753", "1S", "1D P"],  # p48, h7
        ["QJ5.J753.KT8.A42", "1N", "1D P"],  # p48, h8
        ["A643.KJ63.J7.J53", "1D", "1C P"],  # p48, h9
        ["A643.KJ63.J7.J53", "2D", "1D P"],  # p48, h9 (Possibly 1N)
        ["KJ953.K76.K83.J7", "3C", "1C P"],  # p48, h10
        ["KJ953.K76.K83.J7", "2C", "1D P"],  # p48, h10

        # In this hand we have 10 support points but only 5 HCP.
        # FIXME: How does this interact with length points?
        [".KT953.Q863.T742", "2D", "1D P"],

        # FIXME: I think this result is wrong.  Should we mention a second minor or raise partner?
        ['AKQJ6.T863.9.J54', '3N', 'P 1C P 1D P 2N P', 'N-S'],  # deal 4285488505698364167172343412243, S should prefer 3N over 5C.

        # With no major to explore, the best we can do is bid 1N?  Or should we play our partner for 4 clubs?
        ['QJ32.AKQ.432.432', '1N', '1C P'], # from none-finder
        # Partner likely has 4, so maybe a limit raise with 12 is OK?
        ['432.AJ32.AKT.432', '3D', '1D P'], # from none-finder
    ],

    "test_game_forcing_response_to_one_of_a_minor": [
        # Responding with game-forcing values
        # FIXME: The book recommends bidding 2NT over 1C here, however 1D is equally forcing.  (Partner could be 6-5 and reversing, no?)
        ["Q73.KJ65.KJ3.K75", "2N", "1C P"],  # p49, h11 (Some partners respond 3N! may need option.)
        ["Q73.KJ65.KJ3.K75", "2N", "1D P"],  # p49, h11 (Some partners respond 3N! may need option.)
        ["98.J732.AQJ74.AQ", "1H", "1C P"],  # p49, h12
        ["98.J732.AQJ74.AQ", "1H", "1D P"],  # p49, h12
        ["QJ5.A75.KT87.A42", "1H", "1C P"],  # p49, h13
        ["QJ5.A75.KT87.A42", "1H", "1D P"],  # p49, h13

        ['QJ52.AKQ7.97.KJ2', '3N', '1D P'],  # 16 hcp
        ['QJ52.AKQ7.97.KQ2', '3N', '1D P'],  # 17 hcp

        ['AKJ.5432.Q32.AKQ', '3N', '1D P'], # 19hcp, despite what the book says (16-18hcp) 3N needs to be uncapped.

        # Game forcing strength and too big to limit raise.
        # Maybe we should jump to 2N here even though not balanced, give partner a chance to show something else?
        ['AJ9853.K.T54.KQJ', '4C', '1C P'],  # 2-d9b5da4882e3635ca730883f57, E
        ['Q8.AQ9632.AT.J43', '4D', '1D P'],  # 6-ec87e494127d1eb3a4c45bc86e, E
        ['AKJ973.5.T98.AQ5', '4C', '1C P'],  # 11-6166228f84d41073ab743bfde6, S

        # A new suit is uncapped, slow arrival.
        ['AQJ93.AJ643.A87.', '2C', '1D P'],  # 15-23d2eb8a61cb67de9548c7d130, S
        ['T9632.AKJ52.K.K5', '2C', 'P 1D P'],  # 8-a3b69327b038a5751de348077b, S
    ],

    "test_slam_zone_response_to_one_of_a_minor": [
        # Slam zone bids by responder
        ["AJ3.K76.A8.AKJ75", "2S", "1D P"],  # p49, h14
        # FIXME: h15 and h16 are two < 19 hcp jump-shifts which the book makes on special circumstances.
        # It's not entirely clear how to quantify those circumstances.
        ["AT98.QJ72..AKQT9", "2S", "1D P"],  # p49, h15
        ["K985.3.AKQ987.K2", "2H", "1C P"],  # p49, h16

        # We have the big hand and no 5-card jumpshift, we should take over the auction with Jacoby2N
        # We're going at least to 6 and probably to 7.
        ['AKJ8.J42.AKJ.KJ4', '2N', '1H P', 'Both'],  # 10-a00db3fb841e695a077cb618dd, W
    ],

    "test_minimum_rebid_by_opener": [
        ["KQ8.AJ.9765.A987", "2H", "1C P 1H P"],  # p51, h1
        ["KQ87.AJ.976.A987", "1S", "1C P 1H P"],  # p51, h2
        ["KQ875.AJ.976.A98", "1N", "1C P 1H P"],  # p51, h3

        ["86.T4.AKJ753.A98", "2H", "1H P 1S P"],  # p52, h4
        ["QJ87.J6.AKJ75.K8", "2C", "1H P 1S P"],  # p52, h5

        ["K92.34.K4.AKQT87", "2S", "1S P 1N P"],

        # Rebid our 6-card (in this case 7!) suits in preference to nt-escape.
        ['95.85.K6.AKQ8764', '2S', 'P 1S P 2C P'],  # 1-39edeca8410afb072c9e115ed5, E

        # Partner has denied support for hearts, NT slam is remote (max 30 hcp), Pass.
        ['A4.Q2.J864.AJT63', 'P', 'P 1S P 3N P', 'Both'],  # 10-f970d1a53c42cdb89e43b6d286, S

        # We're (barely) a minimum, we don't like partner's suit, and RHO has claimed the majors, we just pass?
        ['AT86.J.AT74.AJ84', 'P', 'P 1C P 1D X', 'N-S'],  # 15-49dcc1d485ac66e70dadb0b8e3, W

        # We have a fit for partner's diamonds, but we'd still rather be in a major if possible.
        # If we're gonna find a game it's going to be due to partner's big hand, so maybe
        # we should support his diamonds and hope he bids 3S to show delayed support?
        ['K.A9763.6.AJT752', '3D', '1S P 2D P'],  # 1-af75b4d3c21a8e539ae491343c, N

        # In a 2-over-one auction, we rebid our suit with a minimum.
        ['K32.KQJT9.QJ32.T', '2D', 'P 1D P 2C P', 'E-W'],  # 3-f1158b5861ffdf222bd8998381, W
    ],

    "test_invitational_rebid_by_opener": [
        # h6, h7, h8 are not precicely covered in the book.  Bids are my inferences.
        [".AKT42.Q63.AK754", "4S", "1S P 2S P"],  # p52, h6
        ["K3.AJ6.K64.KQ542", "2N", "1S P 2S P"],  # p52, h7
        ["A2.KQ5.KJ7.KJ432", "2N", "1S P 2S P"],  # p52, h8

        ["K98.A97.AQ765.A9", "2N", "1H P 2H P"],  # p52, h9
        ["K9.A976.AQ765.A9", "3D", "1H P 2H P"],  # p52, h9 (modified per comments on page)
        ["K73.A3.AJ7654.A9", "3H", "1H P 2H P"],  # p52, h10

        ["K7.AJ843.KQ74.A9", "2H", "1D P 1S P"],  # p53, h11
        ["KQ87.AJT4.9.A987", "3S", "1D P 1S P"],  # p53, h12
        ["KQJ87.3.74.AQT98", "2S", "1S P 2H P"],  # p53, h13
        ["KQ8.AJT.A8.AT987", "2N", "1S P 1N P"],  # p53, h14
        ["KJ86.K4.A8.KQ632", "3C", "1S P 2S P"],  # p53, h15

        ["A532.AK52.J4.AQ9", "2N", "P 1D P 1H P"],

        ["AKJ43.AKJ4.432.4", "2D", "1C P 2C P"], # 2D is the lowest HelpSuitGameTry.

        # Up the line with 4 card suits.
        ['AK86.AJT8..AQ653', '3C', '1S P 2S P', 'N-S'],  # 5-ef236c1d9c42c655a7ed206acc, N

        # Better to rebid a major than mention a new minor?
        ['2.7643.AKQ986.AK', '3H', '1H P 2C P', 'E-W'],  # 3-84451c4ae81f4f7ba4a9137fca, S

        # We're almost game-forcing, likely heading to 2N, showing clubs is probably most helpful?
        ['AKJT.AQJ652.3.Q3', '2C', 'P 1D P 1N P', 'Both'],  # 4-96e6080b0ef0cc55dae51eeb4d, N
    ],

    "test_game_forcing_rebid_by_opener": [
        ["KQ9.AJ98.A4.A987", "4S", "1D P 1S P"],  # p54, h16, FIXME: Would be fixed by using support points in fallback bidder.
        ["K7.AK875.K4.AK87", "2S", "1D P 1H P"],  # p54, h17, FIXME: Teach bot how to bid Reverses.
        ["KQ.AJT.K87.A9876", "4H", "1S P 2H P"],  # p54, h18
        ["K5.AJ9.AKJ984.A9", "4H", "1H P 1N P"],  # p54, h19 (Maybe 3H?)
        ["K765.AK87.KQ.A98", "2N", "1D P 1H P"],  # p54, h20
        ["K4.AKQJ94.87.A96", "3N", "1D P 1H P"],  # p54, h21

        # JumpShift is forcing and thus better than rebidding to show 6 hearts.
        ['AKJ5.Q2.AQ9842.A', '3C', 'P 1H P 1S P'],  # 8-7855840deedca11a0d32bf79b8, N
        # JumpShift is better than a help-suit (even skipping 3N?)
        ['KQ.QT96.AKJT5.A9', '4D', 'P P 1H P 2H P', 'N-S'],  # 15-fbd9a0694f04a9c9e0c16dd2f4, N

        # This is a jumpshift, not doubling hand:
        ['AKQT54.J.AK54.A5', '3H', '1C 1D P 2D', 'N-S'],  # 5-a0f9103e6691db09bfc153a7b4, N

        # We'd rather jump to 3N (game force) than bid 2N (invitational)
        ['Q742.AK9.KT3.AK7', '3N', 'P 1C P 2C P', 'Both'],  # 7-ddb65e2226c9f3801c3a11d66f, W

        ['AKJT62.AKQJ.7.Q7', '3D', 'P P P 1C P 1S P', 'E-W'],  # 6-1e3704155bd007787edbaa2acb, N

        # Even though partner is week, seems better to show our full points instead of just jumping to 4S.
        ['9.K95.AKQ6.AKJ75', '4H', 'P P P 1S P 2S P', 'Both'],  # 4-cdde3c43bd9d843873a918958a, S
    ],

    "test_opener_rebid_after_a_limit_raise": [
        ["Q6.Q86.KT5.AQ982", "P", "1S P 3S P"],  # p55, h22
        ["6.KJ86.KT5.AQ982", "4S", "1S P 3S P"],  # p55, h23
        ["98.Q86.KT5.AKQJ8", "4S", "1S P 3S P"],  # p55, h24

        # With length-points we have enough to justify game?
        ['9.Q974.AJ852.AK9', '4H', '1H P 3H P', 'Both'],  # 10-eea930810769b79341c4f2b7b5, E

        # We have unmentioned heart strength, game is ours.
        ['J7.A.AJ87432.K92', '4H', 'P P 1H P 3H P'],  # 1-d46de04d1347ea928e0a53f8db, S

        # We've got a part score and nothing more.
        ['KQ98.98.KJ98.KT9', 'P', '1C P 3C P', 'E-W'],  # 9-a5e0a0bbdc3ad67708c56b50f1, N

        # 3H seems a reasonable help-suit here?
        ['KQ43.T.AK76.AQT3', '3H', '1C P 2C 3D', 'Both'],  # 13-817aa06f5f8fbf90e741265c48, N

        # Game seems like a great idea with 15 hcp.
        ['T942.84.AK.AQJ85', '4S', '1S P 3S P', 'E-W'],  # 9-32d42d7cf49a96b7f98293490c, N

        # With a minimum (and vulnerable) game seems unworth the risk?
        ['AT5.9.AJ964.A873', 'P', 'P P P 1H P 3H P', 'N-S'],  # 2-945e3a17db2d5f3288f11e06e8, N
        ['AQ2.A963.8.K9872', 'P', '1S P 3S P'],  # 11-853fcb98ec8d2d44bd56cca918, S

        # Accept the game if we see it!
        ['87.T9.AKT85.AKQ5', '4H', '1H 2C 3H P', 'E-W'],  # 9-d9c25a69f70adb4e1182f1fe40, N
    ],

    "test_reverses": [ # Chap 7
        ["2.AKJ72.K973.AJ3", "2H", "1D P 1S P"],  # p60, h1
        ["T.8.AKJ762.AKT32", "2S", "1H P 1N P"],  # p60, h2

        # BOOK_ERROR: Says this should be 2H, but slam should be remote with a 1N response, don't miss game!
        ["A.KJT96.AKT7.KJ9", "3H", "1D P 1N P"],  # p60, h3 (3H may be better/more intuitive)

        ["2.AKJ94.AQJ642.Q", "3D", "1H P 1S P"],  # p60, h4
        ["AQ97.KQ7.JT7.AK4", "2N", "1C P 1S P"],  # p60, h5
        ["AQT542.AQJ.A.987", "2D", "1C P 1H P"],  # p60, h6
        ["AQT542.AQJ.A.987", "2D", "1C P 1S P"],  # p60, h6
        ["AQT542.AQJ.A.987", "3S", "1C P 1S P 2D P 3D P"],  # p60, h6

        # FIXME: Need bid-history-only test for "Another type of reverse"

        # Responder's rebid after the reverse
        # "Lebensohl after opener's reverse" aka "Ingberman 2N"
        # FIXME: We pass this for the wrong reasons.  Retreating to 2N after a forcing bid.
        ["J932.QJ7.Q83.JT3", "2N", "1C P 1N P 2D P"],  # p62, h7

        # Rebidding a 5-card major when forced to.
        ["8763.85.T8.AQ985", "2S", "1D P 1S P 2H P"],  # p62, h8
        ["KQJ62.AK72.KJ8.5", "2N", "1C P 1S P 2D P 2S P"],  # p63
        ["AKJ762.KQ72.K9.5", "3C", "1C P 1S P 2D P 2S P"],  # p63
        ["AQJ76.AK72.J.K75", "3S", "1C P 1S P 2D P 2S P"],  # p63

        ["87632.8.T86.AQ98", "2N", "1D P 1S P 2H P"],  # p64, h9
        # FIXME: Should have a test of opener re-bidding his diamond over 2N

        # FIXME: Why open this 1D?  Seems likely to miss the 5-3 heart fit?
        # BOOK_ERROR: Ignoring this test.  Should open 1H planning to Jump-Shift to 3D.
        # [".AKJ974.AKQJ7.J7", "4H", "1D P 1S P 2H P 2N P"],  # p64
        # FIXME: Need bid-history-only tests for reverse responses p64, p65
        # May need tests for h10, h11, h12, h13 on p66.

        # Partner didn't use Ingberman, so we definitely have game, no fit, so 3N it is.
        ['KQT965.A5.KQ76.A', '3N', 'P 1C P 1S P 2H P 3S P', 'N-S'],  # 15-5bc3ef62e10530af9af2685543, W

        ['K.T986.T74.AKJ72', '3C', '1D P 1S P 2H P', 'E-W'],  # 16-2ecca1239d5bf07906fd2c4a65, E
    ],

    "test_subsequent_bidding_by_responder": [ # Chap 8
        # Subsequent bidding by responder
        # Rebids with weak hands
        ["T64.652.KT54.A54", "P", "1D P 1H P 2H P"], # p69, h1
        ["K953.972.T986.A9", "1N", "1D P 1H P 1S P"], # p69, h2
        ["75.K53.K98743.98", "2H", "1C P 1H P 1N P"], # p69, h3
        ["K8754.Q9.76.J984", "2C", "1C P 1S P 1N P"], # p70, h4
        # When partner has offered 2 suits w/o reversing, he may up to 18 points
        # but he likely doesn't.  We pick between his two offered suits
        # and in this case, it seems we should pass, preferring 2C (and possibly missing a NT game).
        ["JT64.K532.8.A543", "P", "1H P 1S P 2C P"], # p70, h5
        ["K9.9732.K9.JT943", "2H", "1H P 1S P 2C P"], # p70, h6

        # Game is very unlikely, but not impossible.  We'll have no trouble making 3C.
        ['A873.QJ8643.T5.9', '3C', '1S P 1N P 2C P'],  # 1-60eb708ae67af767784c500bc5, S

        # Invitational rebids
        ["KJ64.652.KT.A754", "2N", "1H P 1S P 2D P"], # p70, h7
        ["K95.97.KQJ986.J9", "3H", "1C P 1H P 1S P"], # p70, h8
        ["Q5.KJ65.K9.Q8762", "3D", "1H P 1S P 2D P"], # p70, h9

        ['J642.K97.KQ6.AJ4', 'P', '1C P 1D P 1N P 2D P', 'E-W'],  # 9-332687aaf2252d73b90dcd5934, N

        # Despite having junk, the book p69 h3 thinks we should escape to a part score.
        # This causes these bids to have a huge range of points, sadly.
        ['Q976.AT8432.T8.9', '2D', '1C P 1D P 1N P'],
        ["KT76.Q.QJ8654.72", "2H", "P P 1D P 1H P 1N P", "E-W"],  # deal 11132096549145279831166942029099 E

        # Forcing rebids
        ["KJ642.KT.KQT97.7", "2C", "1D P 1H P 1S P"], # p71, h10 (FSF)
        ["QJ4.T42.K9.A8765", "2N", "1H P 1S P 2D P"], # p71, h11
        ["K873.86.QJ7432.9", "2H", "1S P 1N P 2D P"], # p71, h12 (not forcing)

        # Game-forcing rebids
        ["KJ6.T.KQT97.KQ74", "2S", "1C P 1H P 1N P"], # p71, h13
        ["K54.KQJ87.KQT97.", "3D", "1C P 1H P 1N P"], # p71, h14

        # Seems better to support partner's major than rebid our minor.
        ['.KQJ965.QJT2.A95', '4H', '1C P 1D P 1H P', 'Both'],  # 7-5a95f6b50b3022a5f039f3729c, N

        # Responder Reverse.  Fear not. p65
        ["3.KJ643.AK75.Q65", "2H", "1C P 1D P 2C P"],
        ["KJ643.Q32.AK75.6", "3H", "1S P 2C P 2S P"],

        # Game sign-offs.
        ["KJ64.JT.KQT9.KJ9", "3N", "1D P 1H P 1N P"], # p72, h15
        ["2.KQ43.KQT8.QT98", "4S", "1D P 1H P 1S P"], # p72, h16
        ["3.AQT743.AK95.65", "5D", "1D P 1H P 1N P"], # p72, h17

        # We've found our fit.  8 support points over partner's 16+?  Seems worth a try?
        ['96.KQ65.86.JT874', '4H', '1H P 1S P 3H P'],  # 1-f78e3471afc69448b501e7a683, S

        # 4H is our game.  No need to beat around the bush.
        ['J3.A7.AKJ986.976', '4H', 'P 1D P 1H P 1N P'],  # 8-6dd4e11f490c2748a6e8fe89cd, S

        # Responder rebids in 2-over-1 auctions.
        ["KJ643.9863.A9.K9", "2S", "1S P 2C P 2H P"], # p73, h18
        ["KJT432.K74.KT8.7", "3C", "1S P 2C P 2H P"], # p73, h19
        ["AQ643.KQ75.763.5", "3D", "1S P 2C P 2D P"], # p73, h20
        ["KJ643.A874.T.K97", "3S", "1S P 2C P 2H P"], # p73, h21
        ["KJ643.A874.T.K97", "4S", "1S P 2C P 3C P"], # p73, h21
        ["AJ432.J85.QT7.AQ", "3D", "1S P 2C P 2H P"], # p73, h22 (FSF)
        ["KJ643.K3.K975.65", "2N", "1S P 2C P 2D P"], # p73, h23

        # In SAYC its possible to pass after a minimum rebid, right?
        ['AKQJ2.975.53.964', 'P', '1H P 2C P 2H P'],

        # This was found via the none-finder.  3S isn't even FSF, is it?
        ['Q974.KJT7.J653.J', '4H', 'P 1C P 1D P 2N P 3C P 3H P', 'Both'],  # 4-c8e6f9057b689eeb42135cc5b0, S

        # We don't like his hearts, but 3N seems unlikely with as few as 22 combined hcp, pass?
        ['KQ732.KQ52..K752', 'P', '1C P 1H P 1S P 3H P'],  # 1-0d4f904737542aeadfa8b126d3, N

        # Unfavorable vulnerability, partner continued after our minimum rebid, pass?
        ['A4.QJ7652..K7542', 'P', '1S P 2H P 2S P 3H P', 'E-W'],  # 16-4e00a6f0fe2f594696537ed88c, W

        # No major fit, means 3N it is!
        ['AQJ754.J7.5.Q876', '3N', 'P 1C P 1D P 1S P 3H P'],  # 11-0f3abee58c5c40b0a5658bf971, W

        # Partner is asking us to go to game if we're near the top of our range.  We are.
        ['52.AQ76.AJ93.K76', '4H', '1D P 1H P 2H P 3H P', 'N-S'],  # 12-cb1851a23e07b7a5734c8be46d, W

        # Even if partner bids twice, we can still pass with nothing.  Heck, we like 1S!
        ['87.842.7652.T953', 'P', '1C P P X 1S P'],  # 14-92bd953b430a6e7f8241de1f24, W

        # 1S here is not FSF and is better than rebiding our minor:
        ['74.QJ7532.8.AJ74', '1S', 'P P 1C P 1D P 1H P'],  # 11-d920d3698b4a43d4bcd36c9f86, S

        # Opener has capped his hand, just head straight to 3N?
        ['A9.QJT65.QJ96.A6', '3N', 'P 1S X XX P 1N P', 'E-W'],  # 3-cc29236c5b15cea4114ea9fef1, E

        # 3S is an invite to game, accept!  We actually probably have slam for this board...
        ['KQ843.AKJ82.2.75', '4S', '1D P 1S P 2C P 3S P', 'E-W'],  # 9-4162b0cdf4d20297dfda523e6a, N

        # Partner may have a big hand, but we still don't jump to 3H:
        ['Q4.K8.Q87643.JT2', '2H', 'P P P 1C P 1H P 2D P', 'E-W'],  # 16-b367e2abe45b34301f24957c26, N

        # Looks pretty slam-tastic, despite the lack of fit.
        # Should this be up-the-line, or skip to the major first?
        ['.KQ43.AKJ98.QT42', '3D', 'P 1C P 1H P 2C P', 'N-S'],  # 5-a416416f614bd80af3bfb65b30, W
    ],

    "test_fourth_suit_forcing": [ # Chap 9
        # Fourth Suit Forcing (FSF)
        ["QT72.742.A8.AK97", "2D", "1H P 1S P 2C P"], # p75, h1
        ["T73.K9.A8.KQJ732", "3S", "1D P 1S P 2C P 2H P 3C P"], # p76, h2
        ["T73.K9.A8.KQJ732", "3S", "1D P 1S P 2C P 2H P 3D P"], # p76, h2
        ["T73.K9.A8.KQJ732", "4S", "1D P 1S P 2C P 2H P 2S P"], # p76, h2
        ["KT2.Q8.732.AJT75", "3S", "1D P 1S P 2C P 2H P 2S P"], # p76, h3
        ["KT2.Q8.732.AJT75", "4C", "1D P 1S P 2C P 2H P 3C P"], # p76, h3
        ["J73.K97.Q8.AQJ72", "4S", "1D P 1S P 2C P 2H P 2S P"], # p76, h4
        ["J73.K97.Q8.AQJ72", "3N", "1D P 1S P 2C P 2H P 2N P"], # p76, h4
        ["J73.K97.Q8.AQJ72", "4C", "1D P 1S P 2C P 2H P 3C P"], # p76, h4
        ["J73.K97.Q8.AQJ72", "4D", "1D P 1S P 2C P 2H P 3D P"], # p76, h4
        # FIXME: 1D here seems in direct conflict with the rule that 2N jump is preferred over mentioning a new minor?
        # Maybe the 2N jump requires a spade stopper?
        ["K92.A983.AK2.732", "2S", "1C P 1D P 1H P"], # p76, h5

        # 1S is natural and only requires 6 hcp.
        ["932.A983.82.Q732", "1S", "1C P 1D P 1H P"],

        # Opener's rebid after FSF
        ["AK83.83.KQ974.82", "2H", "1H P 1S P 2C P 2D P"], # p77, h6
        ["QT72.742.A8.AK97", "4H", "1H P 1S P 2C P 2D P 2H P"], # p77, h6-partner
        ["AQJ754.K7.QJ72.6", "3C", "1C P 1D P 1H P 2S P"], # p77, h7
        ["A643.JT7.QJ64.AQ", "3N", "1C P 1D P 1H P 2S P"], # p77, h8 -- FIXME: We have a minimum, why jump to 3N? is 2S FSF a game force?
        # p77, h8 seems a bit light on points, but certainly with 15 we can jump to 3N.
        ["AK43.JT7.QJ64.AQ", "3N", "1C P 1D P 1H P 2S P"], # Modified p77, h8
        ["K732.84.KJ6.AQ72", "2N", "1C P 1D P 1S P 2H P"], # p77, h9
        ["AJT6.AK972.92.K5", "3N", "1C P 1D P 1S P 2H P 2N P"], # p78, h9-partner
        ["J5.Q2.K874.QJ943", "2D", "1D P 1S P 2C P"], # p78 (Cannot bid 2H, as that would be forcing.  Some might bid 2S instead.)

        # Permitted to raise the 4th suit with four (unstopped).
        ["KJ632.8432..AKQ2", "3D", "1C P 1H P 1S P 2D P"],

        # If we've already found a major fit, we can just bid it.  No need for FSF?
        ['KJ9.82.AQT7.A753', '4S', '1C P 1H P 1S P', 'Both'],  # 4-8289ddd229c8ff81b4667770e1, E

        ['AT97.9.AK753.982', '2S', '1H P 1S P 2C P 2D P'],

        # A rebid here is minimum and not delayed support:
        ['987.AT97.A753.82', '3D', 'P P 1C P 1D P 1H P 2H P 2S P'],
    ],

    "test_preemption": [ # Chap 10
        # Preemption
        ["4.Q765.83.KQT932", "2S", ""], # p83, h1
        ["4.Q765.83.KQT932", "2S", "P"], # p83, h1
        ["4.Q765.83.KQT932", "2S", "P P"], # p83, h1
        ["4.Q765.83.KQT932", "P", "P P P"], # p83, h1
        ["Q98.JT8.53.AKT95", "P", ""], # p83, h2
        ["Q98.JT8.53.AKT95", "P", "P"], # p83, h2
        ["Q98.JT8.53.AKT95", "2S", "P P"], # p83, h2
        ["Q98.JT8.53.AKT95", "1S", "P P P"], # p83, h2
        ["Q83.K9.Q8.AQJ874", "1S", ""], # p83, h3 
        ["Q83.K9.Q8.AQJ874", "1S", "P"], # p83, h3
        ["Q83.K9.Q8.AQJ874", "1S", "P P"], # p83, h3
        ["Q83.K9.Q8.AQJ874", "2S", "P P P"], # p83, h3 (Could use 1S), Special (optional) treatment for 4th seat minimum 6-card openers.

        ['Q3.AQ7632.82.J93', '2D', 'P'], # 2o3 is also valid.
        ['Q3.AQ97632.82.J3', '3D', 'P'], # 2o3 is also valid.
        ['Q3.AQ987632.8.J2', '4D', 'P'], # 2o3 is also valid.

        # Do not have a void or an outside major when preempting. p89
        [".Q765.843.KQT932", "P", ""],
        ["3.76.Q843.KQT932", "P", ""],

        # Partner is not inviting when raising, always pass:
        ['QT96.AQT962.T.83', 'P', '2D P 3D P', 'Both'],  # 13-6734134b87088feeb2d51b4a5e, N
        ['4.QT2.AQJ9862.82', 'P', '3H P 4H P', 'N-S'],  # 2-34fa82d02a19f4c75d453b92be, E

        # We can have an opening hand and still pass:
        ['63.KQT763.J43.AJ', 'P', '1C 2S P', 'N-S'],  # 5-75caa02e3db3cbd853096948d7, W

        # Responding to a new suit from partner after preempt
        ["9.QJ2.AQT984.986", "3S", "2H P 2S P"], # p85, h4
        ["Q9.QT82.AQT984.2", "3D", "2H P 2S P"], # p85, h5
        ["74.982.AQT984.82", "3H", "2H P 2S P"], # p85, h6

        # With a maxium and no fit for partner, bid Notrump:
        ["74.982.AKQT94.82", "2N", "2H P 2S P"],
        # p 90 seems to suggest we might bid 3N here?  Rebidding 3S, even with a maximum seems better, let parter call NT?
        ["74.982.82.AKQT94", "3N", "2S P 3C P"],

        # Feature bidding over 2N response from partner to your preempt
        ["T9.982.AKT984.98", "3H", "2H P 2N P"], # p85, h7
        ["T9.KT2.AQT984.82", "3D", "2H P 2N P"], # p85, h8
        ["J9.QT2.KQJ984.J2", "3D", "2H P 2N P"], # p85, h9

        ['T32.Q63.KQJ986.2', '3H', 'P 2H P 2N P', 'Both'],  # 13-58e04ce61e0da8e75d5d2383bb, E - despite a protected queen, 8 hcp is still "minimum"

        # Three level preempts
        ["J4.T.QJT.AJT7653", "P", ""], # p86, h10
        ["J4.T.QJT.AJT7653", "P", "P"], # p86, h10
        ["J4.T.QJT.AJT7653", "3S", "P P"], # p86, h10
        ["J4.T.QJT.AJT7653", "1S", "P P P"], # p86, h10 (Ro15)
        ["J64.85.KQT9852.5", "3H", ""], # p86, h11
        ["J64.85.KQT9852.5", "3H", "P"], # p86, h11
        ["J64.85.KQT9852.5", "3H", "P P"], # p86, h11
        ["J64.85.KQT9852.5", "P", "P P P"], # p86, h11
        ["A976432.65.KJT.7", "P", ""], # p86, h12
        ["J97.AKJ9852.98.7", "3D", ""], # p87, h13
        ["J97.AKJ9852.98.7", "3D", "P"], # p87, h13
        ["J97.AKJ9852.98.7", "3D", "P P"], # p87, h13
        ["J97.AKJ9852.98.7", "P", "P P P"], # p87, h13
        ["AKQ985.T987.62.9", "3C", ""], # p87, h14
        ["AKQ985.T987.62.9", "3C", "P"], # p87, h14
        ["AKQ985.T987.62.9", "3C", "P P"], # p87, h14
        ["AKQ985.T987.62.9", "P", "P P P"], # p87, h14
        ["A.5.9842.AT98654", "P", ""], # p87, h15
        ["J4.QT6.KQJT872.4", "3H", ""], # p87, h16
        ["J4.QT6.KQJT872.4", "3H", "P"], # p87, h16
        ["J4.QT6.KQJT872.4", "3H", "P P"], # p87, h16
        ["J4.QT6.KQJT872.4", "P", "P P P"], # p87, h16
        ["J7.5.A92.KT87654", "P", ""], # p87, h17

        # Responses to preempts
        [".K5.A985.KJ76432", "P", "3C P"], # p88, h18
        ["KJ74.JT95.9732.A", "5C", "3C P"], # p88, h19
        ["Q4.A7.K84.AKJT74", "3S", "3C P"], # p88, h20
        ["T9842.A95.A3.AK5", "3N", "3S P"], # p88, h21
        ["K4.A87643.82.983", "4S", "3S P"], # p88, h22
        ["A9432.A8652.AKQ.", "4S", "3S P"], # p88, h23
        ["864.AKQT6.A2.K83", "5S", "3S P 4N P 5C P"], # p88, h24
        ["864.AKQT6.A2.K83", "6S", "3S P 4N P 5D P"], # p88, h24

        # If he has an outside entry 3N is trivial.
        ["AKQ83.AKT93..A85", "2N", "2H P"], # bidder-fight 13-245b5abb34a4a431f051f8ecde

        # 50% 3N seems worth the gamble?
        ['74.K6.AQ8.KQJ983', '3N', '3C P', 'Both'],  # 10-5d3926683428d109caced97cfe, W

        # Partner's 3N is not inviting to 4N:
        ['AK7432.42.62.Q87', 'P', '3C P 3N P', 'Both'],  # 7-ab60c6a6737408d94f47ffa520, S

        # 10 clubs and all suits stopped, 3N should be easy.
        ['A53.K5.AKJ72.QJ3', '3N', '3C P'],  # 8-d1be3f6a42806431fd944f2a5e, E
        # Same idea, everything stopped, and have at least one club to lead to partner.
        ['Q.A652.AQ962.AK9', '3N', 'P 3C P', 'Both'],  # 13-6a465d32f4817dae76ee040e0f, W
        ['AK.JT962.A4.AT97', '3N', 'P 3C P', 'N-S'],  # 5-118157f932fc16e1620ea4dfab, W

        # This looks very slammy from our side.  We see 7 club QTs and at least 5-6 heart tricks from partner.
        ['AKQJ852.KT2.Q96.', '2N', 'P 2H P'],  # 1-d38ebff0963ac68d71d690504a, W

        # Four level preempts
        ["KT3..74.AJT87432", "4S", ""], # p88, h25
        ["KT3..74.AJT87432", "4S", "P"], # p88, h25
        ["KT3..74.AJT87432", "4S", "P P"], # p88, h25
        ["KT3..74.AJT87432", "1S", "P P P"], # p88, h25
        ["3.KT5.A.KQT98642", "1S", ""], # p88, h26 (my guess.  Rule of 15 open)
        ["8.9873.AKQT864.4", "4H", ""], # p88, h27
        ["8.9873.AKQT864.4", "4H", "P"], # p88, h27
        ["8.9873.AKQT864.4", "4H", "P P"], # p88, h27
        ["8.9873.AKQT864.4", "4H", "P P P"], # p88, h27

        # Partner shouldn't have more than 2 spades preempting in first seat, so 5C should be almost a laydown.
        ['A4.AK87652.A.J42', '5C', '4C P', 'Both'],  # 4-f7f3af5c5522528c0b251bb84a, E

        # We have the majority of the points, but only barely.  They stole our potential game, double.
        ['AK92..K32.QT8754', 'X', '1S 3D 3S 5D'],  # 14-72898d4e2ae885bc3fd3145d1e, E

        # Partner has passed.  Better to preempt than search for a fit.
        ['Q842..Q42.AK9753', '2S', 'P P 1D', 'Both'],  # 10-22e151e6eeb7f119772d2313a0, N
    ],

    "test_preemptive_overcalls": [
        # The book covers preemptive overcalls with 2 whole sentences.
        # Here are some cases we've come up with to test that with <= 11 points
        # we prefer to preempt, but with 12+ we prefer a standard overcall.
        ["4.Q765.K3.AQJ932", "1S", "1H"],
        ["9.QJ2.AQJ984.K86", "1H", "1C"],
        ["KQ2.QT8.AQJ984.2", "1H", "1D"],

        ["4.T765.83.KQJ932", "2S", "1H"],
        ["9.JT2.AQT984.986", "2H", "1C"],
        ["J9.T982.AQT984.2", "2H", "1D"],

        ['73.AQ7632.8.T932', '2D', '1C'], # 2o3 is also valid.
        ['73.AQ97632.8.T92', '3D', '1C'], # 2o3 is also valid.
        ['73.AQ987632.8.T2', '4D', '1C'], # 2o3 is also valid.

        # 2S seems like a better response than a takeout double.
        ['J843.J8.K.KQJ864', '2S', '1D P 1H', 'N-S'],  # 12-e9386cf73e09c755012d2e27a9, S
    ],

    "test_strong_two_club": [ # Chap 11
        # The Strong 2C Opening, chap 11.
        ["QJ842.AJ5.AK.AQJ", "2C"], # p91, h1
        ["K4.AK.AKQ543.K83", "2C"], # p91, h2
        ["AK.AKJ7.43.AKQT6", "2C"], # p91, h3
        [".A4.2.AKQT985432", "2C"], # p91, h4

        # Responding to a 2C Opener
        ["4.975.K84.KQ7642", "2S", "2C P"], # p92, h5
        ["K4.AQ5432.53.983", "3D", "2C P"], # p92, h6
        ["64.QT87.Q732.AQ6", "2N", "2C P"], # p92, h7
        ["864.84.7562.KJ98", "2D", "2C P"], # p92, h8

        # Opener's rebids after 2C
        ["K876.AK.A2.AKQT9", "2S", "2C P 2D P"], # p93, Opener
        ["QJ95.984.Q76.653", "4S", "2C P 2D P 2S P"], # p93, Responder
        ["K94.AK.AKQT2.AJ3", "6S", "2C P 2S P 4N P 5C P"], # p94, Opener
        ["QJ7.984.53.KQ652", "5C", "2C P 2S P 4N P"], # p94, Responder

        ["K842.AK.AKQ.A974", "3S", "2C P 2D P 2N P 3C P"], # p94, Opener
        ["JT65.764.72.KQ65", "4S", "2C P 2D P 2N P 3C P 3S P"], # p94, Responder
        ["6.AJ3.AK4.AKQJT6", "3S", "2C P 2D P 2S P 3C P"], # p94, Opener, FIXME: If this isn't a self-supporting spade suit, what is?
        ["T954.952.T863.82", "P", "2C P 2D P 2S P 3C P 3S P"], # p94, Responder

        # A jump is game forcing with a self-supporting holding.
        ["K8.AK.A2.AKQT987", "3S", "2C P 2D P"],

        ["QT32.QT8.QJ4.T92", "3N", "P 2C P 2D P 2N P"],

        ['AKQ85.K.AK762.KT', '2H', 'P 2C P 2D P'],  # 1-a9e6b542f0be44052397af31f4, E

        # If second-negative isn't available, pass should be fine?
        ['872.542.9863.J32', 'P', 'P 2C P 2D P 3D P', 'E-W'],  # 9-e23d9177e825572cf297c028da, W
        # Second negative doesn't apply over 2N rebid, that's stayman.
        ['872.542.9863.J32', 'P', 'P 2C P 2D P 2N P'],
    ],

    "test_overcalls": [ # Chap 12
        # Overcalls, chap 12
        ["Q3.AQJ.KQJ83.975", "1H", "1C"], # p98, h1
        ["T98.872.KJ743.T9", "P", "1C"], # p98, h2
        ["AKT.53.KT8.98542", "P", "1H"], # p98, h3
        ["A53.53.987.KJT92", "1S", "1C"], # p98, h4
        ["A53.53.987.KJT92", "1S", "1D"], # p98, h4
        ["A53.53.987.KJT92", "1S", "1H"], # p98, h4
        ["AKJ.Q84.6.AKJT73", "2S", "1H X P 2C P"], # p98, h5
        ["AKJ.Q84.6.AKJT73", "2S", "1H X P 2D P"], # p98, h5
        # This is some sort of exception to the big-hand double rule. The book is worried that
        # the opponents may get to 3S before we have a chance to show our hearts
        # so we should bid them first. I don't understand well enough yet.
        ["AQJ6.K96.AKJ74.3", "1H", "1C"], # p98, h6

        ["JT6.T96.AK874.T3", "1H", "1C"], # 2o3 is also sufficient.

        # Two-Level Overcalls
        ["K8.76.AQ953.QJT2", "P", "1S"],  # p99
        ["QJT2.76.AQ953.K8", "2H", "1S", 'None'],  # p99 (not-vulnerable)
        # The book only mentions this hand in a paragraph, unclear if they
        # really intend for us to pass a 12hcp potential overcall in second seat!
        # Ops are likely to negative double, since we took all their bidding space
        # but is that so bad?
        ["QJT2.76.AQ953.K8", "P", "1S", 'Both'],  # p99 (vulnerable)

        ["53.A8.KQJ873.975", "2H", "1S"], # p99, h7
        # I think the book is wrong here and this should just be michaels:
        ["KQ8765.8.AQT95.9", "2H", "1S"], # p99, h8
        # FIXME: Ideally would test a clubs rebid by h8 here.

        ["KQ873.85.32.AKQT", "1S", "1H"], # Prefer 1S over 2C?

        ['AJ8.T9.AQJT9.KQT', '2H', '1S P 1N', 'Both'],  # 7-ef06184f0e5e80b0d576acb9d6, E

        # Direct overcall of 1NT (these examples are from me), p100
        ["KQ4.AQ8.Q9873.K2", "1N", "1C"],
        ["KQ4.AQ8.Q9873.K2", "1N", "1D"],
        ["KQ4.AQ8.Q9873.K2", "1N", "1H"],
        ["KQ4.K98.KQ873.K2", "2H", "1S"],  # K2 is only a 66% stopper, so we can't bid 1N, but with only 16 points we shouldn't big-hand double.
        ["KQ4.A98.QJ873.K2", "1N", "1C"],  # 1N overcalls are 15-18 according to p100.

        # A 1NT overcall is more descriptive than a takeout double and should be prefered.
        ['A3.KT97.JT3.AQ65', 'X', '1C'], # non-big-hand (14hcp)
        ['A3.KT97.JT3.AK65', '1N', '1C'], # non-big-hand (15hcp)
        ['A3.KQ97.QT3.AK65', '1N', '1C'], # Big-hand-doublable (18hcp)
        # At 19 points we're too big to overcall NT
        ['A3.KQ97.KT3.AK65', 'X', '1C'], # Big-hand-doublable (19hcp)

        # Responding to overcalls
        ["J63.Q843.KT87.J5", "3H", "1C 1H P"],  # p101, h9
        ["J63.Q843.KT8.J75", "2H", "1C 1H P"],  # p101 (my example)
        ["63.Q843.AT87.KQ5", "2C", "1C 1H P"],  # p101, h10
        ["K7.Q876.KJ75.KQ5", "2C", "1C 1H P"],  # p101, h11
        ["K7.Q876.KJ75.KQ5", "3H", "1C 1H P 2C P 2H P"],  # p101, h11, The book says to rebid 3H to show your extra values, partner has already capped at 10hcp, so seems unecessary?
        # FIXME: We should probably have an example of responding with competition?

        ["43.5432.Q2.AKQ42", "1S", "1D 1H P"],

        # Cuebids should use support points.
        ["J843.4.KQ43.Q842", "2D", "1D 1H P"],

        # Preemptive jump overcalls
        ["J63.K43.KQT874.5", "2H", "1D"],  # p101, h12
        ["6.Q84.AQT8764.65", "3H", "1D"],  # p101, h13
        ["874..AQT87642.Q5", "4H", "1D"],  # p101, h14
    ],

    "test_michaels_and_unusual_notrump": [ # Chap 13
        # Michaels cue-bid
        ["AK.J.T8753.JT432", "P", "1C"],  # p104, h1
        [".754.AQJ97.QT984", "2C", "1C"],  # p104, h2
        [".754.AQJ97.QT984", "2D", "1D"],  # p104, h2
        ["AJ943.KQ.9.AKT95", "4S", "1H 2H P 3S P"],  # p104, h3
        ["5.3.KJT87.QT9865", "2C", "1C"],  # p104, h4
        ["5.3.KJT87.QT9865", "2D", "1D"],  # p104, h4
        ["Q9863.Q4.J.KQT87", "1S", "1H"],  # p104, h5
        ["4.QJT876.AQT86.5", "3D", "1S 2S P 3C P"],  # p104, h6
        ["Q6.3.KQT87.AQ986", "1S", "1C"],  # p105, h7
        ["Q6.3.KQT87.AQ986", "1S", "1D"],  # p105, h7
        ["A.Q4.KQT87.KQT87", "2C", "1C"],  # p105, h8
        ["A.Q4.KQT87.KQT87", "2D", "1D"],  # p105, h8
        ["86.3.QJT43.AK865", "2D", "1D P 1N"],  # p105, h9
        [".54.KJT65.QJT875", "2C", "1C P P"],  # p105, h10
        [".54.KJT65.QJT875", "2D", "1D P P"],  # p105, h10
        ["QJ972.A3..AKT653", "3H", "2H"],  # p105, h11

        # Regardless of which minor he has, we want to be in it.
        ['QJT9763.AQ43.A4.', '4C', '2H 3H P'],  # 11-125d5625bef1d842faa60c0cbf, E

        # FIXME: If we have a max-michaels, partner likely doesn't have much, jump to show him we want this?
        # I can't find this in the book.  Maybe we invented it for the KBB?
        ['KJ984.93.KJ986.2', '4C', '1S 2S P 2N P'],
        ['Q3.AKJ94.AKJ86.2', '4D', '1S 2S P 2N P'],
        ['K9874.3.AQ.AKQ72', '4C', 'P 1H 2H P 2N P'],  # 14-0e3f5b9e514a9894a6cf10c93f, W should jump to show his max-michaels?

        # Unusual notrump
        ["QJ9864..KQT87.86", "2N", "1D"],  # p106, h12
        ["AJ986.KQT875..87", "2N", "1H"],  # p106, h13
        ["AJ986.KQT875..87", "2N", "1S"],  # p106, h13
        ["4.QJT876.KQT86.5", "2N", "1C"],  # p106, h14
        ["4.QJT876.KQT86.5", "P", "1D"],  # p106, h14
        ["4.QJT876.KQT86.5", "P", "1H"],  # p106, h14
        ["4.QJT876.KQT86.5", "2S", "1S"],  # p106, h14
        ["4.QJT876.KQT86.5", "P", "2C"],  # p106, h14
        ["4.QJT876.KQT86.5", "P", "2D"],  # p106, h14
        ["4.QJT876.KQT86.5", "P", "2H"],  # p106, h14
        ["4.QJT876.KQT86.5", "3S", "2S"],  # p106, h14
        ["AQJ98.A.KQJT8.86", "2N", "1D"],  # p107, h15
        ["AQT987.AKQT8.4.A", "4N", "1H"],  # p107, h16
        ["AQT987.AKQT8.4.A", "4N", "1S"],  # p107, h16

        ['JT876.92.JT754.4', 'P', 'P 1D'], # Insufficient points.

        # p107 says 2N is unususal over 2C, but shows a strong 2N over preempts:
        ['KT987.KQT87.43.2', '2N', '2C'],
        ['KT987.KQT87.43.2', 'P', '2S'],
        ['KT98.KQ2.AK4.KQT', '2N', '2S'],

        # Michaels/Unusual notrump in the balancing seat
        ["2.3.QJ8752.KT984", "2D", "1D P P"],  # p107 (BOOK_ERROR: The hand only has 12 cards in the book!)
        ["KQ4.AQ8.KQ873.K2", "2N", "1D P P"],  # (my example) p141 points out that 2N in the balancing seat is not Unusual.  Why would we ever jump to 2N instead of start with a double?
        ['Q4.AKJ92.AQT65.T', '1H', '1C P P'],  # 8-19d138e4c788a3e87b89f5125f, S

        # Can't leave partner in 2N, at least pick one:
        ['86.A92.84.KJ8732', '3D', 'P 1C 2N P', 'N-S'],  # 5-6731f54beb3ac91e29ec190931, N
        ['4.AT93.Q84.QT953', '3H', '1D 2N P', 'E-W'],  # 3-c70feaa630589e606f7c7625d0, E
    ],

    "test_responses_to_michaels": [
        # Michaels minor request:
        ['KJ984.93.KJ986.K', '3C', '1S 2S P 2N P', 'N-S'],  # deal 6177852048991998477340369815114, N should respond with his minor when asked.
        ['93.KJ984.KJ986.K', '3D', '1S 2S P 2N P', 'N-S'],  # modified from deal 6177852048991998477340369815114, N should respond with his minor when asked.
        ['KJ984.93.KJ986.2', 'P', '1S 2S 3S 4C P'], # This is not covered in the book, but seems reasonable.
        ['93.KJ984.KJ986.2', '4D', '1S 2S 3S 4C P'],
        ['KJ984.93.KJ986.2', '5C', '1S 2S 4S 4N P'],
        ['93.KJ984.KJ986.2', '5D', '1S 2S 4S 4N P'],

        # FIXME: Maybe we should use michaels minor request to get his point-range first?
        ['K75.AQ5.542.T763', '3H', 'P 1S 2S P'],  # 11-c66f5e1c834268a144ccb69edf, S

        # 2N is to play in response to a minor michaels.
        ['AJT952.AJT9.53.9', '2N', '1D 2D P', 'N-S'],  # 12-b6feacbc53abe224151d4c3845, S
    ],

    "test_overcalling_one_notrump": [ # Chap 14
        # Cappelletti
        ["Q52.K97.3.AQJ764", "2S", "1N 2C P 2D P"],  # p110, h1
        ["3.86.AQT75.KQ632", "2D", "1N"],  # p110, h2
        ["AKJ42.T9.AQ875.5", "2H", "1N"],  # p110, h3
        [".KQT73.642.AQJ84", "2S", "1N"],  # p110, h4
        ["KJT643.AQT62..87", "2N", "1N"],  # p110, h5
        ["AKJT742.Q97.65.5", "3C", "1N"],  # p110, h6
        ["AQJ7642.T9.3.852", "P", "1N 2C P"],  # p111, h7
        ["865.96.J984.Q632", "2D", "1N 2C P"],  # p111, h8
        ["542.T9.AQJT65.53", "2H", "1N 2C P"],  # p111, h9
        ["872.AQJT73.42.84", "P", "1N 2D P"],  # p112, h10
        ["QT643.JT62.4.873", "2S", "1N 2D P"],  # p112, h11
        ["9742.QJ7.QJ65.A3", "3H", "1N 2D P"],  # p112, h12
        ["T76432.QJT732.4.", "2N", "1N 2D P"],  # p112, h13
        ["AKQT643.T62.4.73", "3C", "1N 2D P"],  # p112, h14
        ["Q872.T73.742.842", "P", "1N 2H P"],  # p112, h15
        ["QT643.T962.4.965", "2N", "1N 2H P"],  # p112, h16
        ["A742.QJ7.QT65.83", "3H", "1N 2H P"],  # p112, h17
        ["76.72.42.KQT9843", "2S", "1N 2H P"],  # p112, h18
        ["AK43.T62.KT43.73", "3H", "1N 2H P 2N P 3C P"],  # p112, h19
        ["AK43.T62.KT43.73", "3H", "1N 2H P 2N P 3D P"],  # p112, h19
        # Sanity check that we know how to respond to a minor request:
        ["AKJ42.T9.AQ875.5", "3C", "1N 2H P 2N P"],

        # Breath a sign of relief and pass.
        ['63.J873.9874.T73', 'P', '1N X 2C', 'E-W'],  # 16-2791340b7a497786a5f38c86fc, S
        ['9875.J82.83.9854', 'P', 'P P 1N X 2H', 'E-W'],  # 9-b1d53bdfb1a4f9384ca81714a8, E

        # Cheapest available?
        ['T9.2.KJ753.T9743', '2H', 'P P 1N X P'],  # 1-8c0d7edab3c0ad9da1dc50658e, E

        # Overcalls at the 3 level are natural:
        ['4.AKQJT83.T5.K52', '3D', '1N', 'N-S'],  # 12-61e69af17c8009cb537cd25ea3, N
        ['K75.J.Q8.KQJ9874', '3S', 'P 1N', 'Both'],  # 13-d6e476331ccb540cb394e5a8ab, S

        # Should weak 1-suited hands go through Cappelletti?
        ['4.AKQJT83.T5.T52', '3D', '1N', 'N-S'],

        # If partner ignores us, just bid our suit:
        ['QT62..KJ8763.KJT', '2H', '1N 2C X P P', 'E-W'],  # 16-372932667d6df870144eeda832, N
    ],

    "test_doubles": [ # Chap 15
        # Penalty Double
        ["T98.KQ4.863.Q875", "P", "1N X P"],  # p116, h1
        ["J7.872.53.QJ9874", "2S", "1N X P"],  # p116, h2
        ["JT9872.87.86.JT9", "2C", "1N X P"],  # p116, h3 (Note: not stayman! RHO bid of 2C would have been stayman.)
        ["7643.5.Q9843.432", "2H", "1N X P"],  # p116, h4

        # Takeout Double
        ["KJ98.AQJ7.3.Q875", "X", "1H"],  # p117, h5
        ["KJ76.KQ72..J9874", "X", "1H"],  # p117, h6
        ["AK92.AQ87.JT8.92", "P", "1H"],  # p117, h7
        ["A92.K62.QJ965.A7", "P", "1H"],  # p117, h8
        ["3.A6.KJ983.Q8754", "X", "1C P 1D"],  # p118, h9
        ["Q87.AQ62.3.AK874", "1S", "1H"],  # p118, h10

        ["KT843.AQ9.KT87.T", "X", "3S"],  # Takeout double of preempt.
        ["2.AK742.KJ7.QJ64", "X", "3C P P"],

        # No point in doubling when RHO has shown a big hand.
        ['KQ76.Q5.A962.764', 'P', '2S P 3D'],  # 14-f60b50eb1e9cf2638ad14c2597, N

        # Bighand doubles work after preempts too:
        ['AKQ6.Q9.AKT84.K8', 'X', '2D', 'E-W'],  # 6-c097fa8c5d96d39c9b6b10234b, S
        # If we're not big-hand, we'd rather overcall?
        ['KQT6.T9.AKT84.K8', '2H', '2D', 'E-W'],

        ['K2.A3.KQJ72.AQ54', 'X', 'P 2D', 'E-W'],  # 9-bc5ccef8c155683612a069fd2e, S

        # Doubling to show show strong holdings
        ["A87.AK96.8.AK875", "2S", "1H X P 1S P"],  # p118, h11
        ["A87.AK96.8.AK875", "2S", "1H X P 1N P"],  # p118, h11
        ["A87.AK96.8.AK875", "2S", "1H X P 2C P"],  # p118, h11
        ["A87.AK96.8.AK875", "2S", "1H X P 2D P"],  # p118, h11
        ["A87.AK96.8.AK875", "2S", "1H X 2C P 2H"],  # p118, h11
        ["A87.AK96.8.AK875", "2S", "1H X 2D P P"],  # p118, h11
        ["KJ7.AJ6.KJ7.AQ86", "X", "1C"],  # p118, h12
        ["KJ7.AJ6.KJ7.AQ86", "X", "1D"],  # p118, h12
        ["KJ7.AJ6.KJ7.AQ86", "X", "1H"],  # p118, h12
        ["KJ7.AJ6.KJ7.AQ86", "X", "1S"],  # p118, h12
        ["K2.AKT86.5.AQJ76", "1S", "1C"],  # p118, h13

        ["A874.AK96.8.AK84", "2S", "1H X P 2S P"],

        ['8.KQT53.K.AKQT92', '3S', 'P P 3C X P 3H P', 'E-W'],  # 3-c83708b64b994a8f83ddf8e515, E

        # Even w/o a stopper, 1N to show 18-19 seems reasonable here?
        ["T87.AK9.A98.AK84", "1N", "1C X P 1D P"],

        # Non-jump shows 19-21, jump shows 21-22. p125
        ["A87.AK9.A98.AT84", "2N", "1H X P 2C P"],
        ["K98.AQJ9.AQ7.KQ4", "2N", "1H X P 1S P"], # 21 hcp
        # With no stopper a cuebid to show 21+ seems better than jump to 2N.
        ["98.AKQ.AJ76.AKJ4", "2C", "1C X P 1D P"],

        # 2N is 21-22 and 3N is 23+
        ["A87.AK9.A98.AK84", "2N", "1C X P 1D P"], # 22 hcp
        ["KQ8.AQJ9.AQ7.KQ4", "3N", "1H X P 1S P"], # 23 hcp

        # Prefer majors over nt over minors for rasises:
        ["A.AKJ8.Q763.KJ84", "2S", "1C X P 1S P"],
        ["A8.KQJ9.AQ7.K984", "1N", "1C X P 1D P"],
        ["98.KQJ9.AJ7.AK84", "2D", "1C X P 1D P"],

        # Prefer support over majors over NT.
        ["A.A43.KQJ32.KJ84", "2S", "1C X P 1S P"],
        ["AJ.KQ8.AQ732.K98", "1H", "1C X P 1D P"],
        ["AJ.KJ4.AK73.K982", "1N", "1C X P 1D P"],

        # majors > nt > minors for jump rasises too:
        ["A8.AKQ.A976.KJ84", "3S", "1C X P 1S P"],
        ["A8.KQJ9.AJ7.AQ84", "2N", "1C X P 1D P"],
        ["98.KQJ9.AQ7.AK84", "3D", "1C X P 1D P"],

        # Prefer support over majors for jumps too (NT is never an option if you have the shape to new-suit-jump)
        ["A.AK.AK9876.QJ84", "3S", "1C X P 1S P"],
        ["AJ.KQ.AQJ832.KJ9", "2H", "1C X P 1D P"],

        # FIXME: Should big-hand jump raises really take us to game?
        ["98.KQJ9.AQ7.AKQ4", "4S", "2D X P 2S P"],
        ["98.KQJ9.AQ7.AKQ4", "5D", "2H X P 3D P"],

        # Responding to a takeout double
        # Responding with no intervening bid
        ["T874.876.86.J843", "2C", "1S X P"],  # p119, h14
        ["J7.AJ64.KJ76.986", "3H", "1S X P"],  # p119, h15
        ["J86.QJ2.K74.QT65", "1N", "1S X P"],  # p119, h16
        ["K87.76.AJT8.AQ43", "2D", "1D X P"],  # p120, h17
        ["J783.AJ64.K76.Q8", "2N", "1D X P"],  # p120, h18
        ["QJ83.AQ64.K76.Q8", "3N", "1D X P"],  # p120 (modified h18 to have 13-16hcp)
        ["Q86.J32.K7.AQT65", "4S", "1D X P"],  # p120, h19
        # Responding with an intervening bid
        ["T874.876.6.AK863", "3S", "1D X 1H"],  # p120, h20
        ["A73.7642.K7.Q986", "1S", "1D X 1H"],  # p120, h21
        ["A73.7642.K7.KJ86", "2S", "1D X 1H"],  # p120 (modified h21 to have 10-12hcp)
        # ["KT65 A7 2 AQ8642", "P", "1D X 1H"],  # p120, h22 "book says cuebid opponent's suit", which?

        # When the opponents make a takeout double
        ["A87.KJ765.6.KJ76", "XX", "1H X"],  # p122, h23, unclear why XX is preferred over mentioning the spades.
        ["J3.T9862.Q32.K86", "2H", "1H X"],  # p122, h24
        ["9874.QJ6.J7432.A", "4H", "1H X"],  # p122, h25
        ["Q3.KQT632.32.J86", "3D", "1H X"],  # p122, h26
        ["9864.A65.87.KQ74", "1S", "1H X"],  # p122, h27

        # Jordan/Truscott 2NT
        ["K743.QJ96.Q865.5", "2N", "1H X"],  # p123, h28
        ["Q864.A653.T987.5", "3H", "1H X"],  # p123, h29

        # Depends on the vulenerability?  This looks like a 50% game or so?
        ['K4.J3.KQ3.AK7642', 'P', 'P 1S X 3S P'],  # 14-795dc2f94c38f2cdd4a626843a, S

        # Lead directing doubles
        ["74.876.AKJ987.63", "X", "1N P 2H"],  # p124, h30
        ["AKQ83.95.97.Q986", "X", "1N P 2C"],  # p124, h31
        ["T986542..A7.6532", "X", "1H P 3H P 4N P 5D"],  # p124, h32
        # FIXME: A bunch of bid-only hands we could test from p126.
    ],

    "test_negative_double": [ # Chap 16
        ["74.876.KQ73.A863", "X", "1D 2C"],  # p127, h1
        ["87.A864.K9653.76", "X", "1C 1S"],  # p127, h2
        # FIXME: A bunch of bid-only hands we could test from p129.
        ["9872.K64.K875.63", "X", "1C 1S"],  # p130, h3
        ["73.J986.J53.A864", "P", "1C 2H"],  # p130, h4
        ["64.Q965.984.KQ75", "X", "1C 1H"],  # p130, h5
        # This is really a pass after reopening double for penalty test:
        ["4.A3.KQ65.KJT865", "P", "1C 1S P P X P"],  # p130, h6

        # Negative doubles to show strong hands
        ["KJ52.K9864..AQ64", "3H", "1C 2H X P 2S P"],  # p131, h7 (cuebid)
        ["KJ52.K9864..AQ64", "3H", "1C 2H X P 3C P"],  # p131, h7 (cuebid)
        ["KJ52.K9864..AQ64", "3H", "1C 2H X P 3D P"],  # p131, h7 (cuebid)
        ["KJ3.86.AQT7.K963", "3N", "1D 2C X P 2D P"],  # p131, h8
        ["KJ3.86.AQT7.K963", "4H", "1D 2C X P 2H P"],  # p131, h8
        ["KJ3.86.AQT7.K963", "4S", "1D 2C X P 2S P"],  # p131, h8
        ["KJ4.T9.AJ74.Q875", "2N", "1D 2C X P 2D P"],  # p131, h9
        ["KJ4.T9.AJ74.Q875", "3H", "1D 2C X P 2H P"],  # p131, h9
        ["KJ4.T9.AJ74.Q875", "3S", "1D 2C X P 2S P"],  # p131, h9

        # Responding to a negative double
        ["J5.AQ864.A54.K76", "2D", "1D 1S X P"],  # p131, h10 (1NT is also valid)
        ["KJ43.KQJ97.K5.87", "2C", "1D 1S X P"],  # p131, h11
        ["A94.KQ87.874.KJ6", "1N", "1D 1S X P"],  # p131, h12

        ['KT964.QJ874.53.A', '3C', 'P P 1D 1S X 2S', 'N-S'],  # 15-d2381cacd0b0d88e797add66d4, N

        # Showing a 6-card suit seems better than just showing points:
        ['AKQJT2.QJ5.Q4.A3', '3C', '1C 1S X P'],  # 8-e814ffd1ea2f99d681d2c91423, W

        # Minimum NT responses only show shape, not more points.
        ['AT76.K63.Q98.KJ8', '2N', 'P 1C 2S X P', 'Both'],  # 13-3e5b4b44d80b70f05a7ce29e66, E
        ['A973.KJT82.J43.Q', 'P', 'P 1S 2H X P 2N P'],  # deal 17874141946813701341102482461267
        ['A973.KQT82.Q43.Q', '3N', 'P 1S 2H X P 2N P'],

        # Jump rebids are 16-18hcp p133
        ["A964.KQ874.K7.A8", "2N", "1D 1S X P"],

        ["KJ6.AQJ93.K5.AJ6", "3N", "1D 1S X P"],  # p131, h13, Why 3N instead of 2N?  Minor followed by 2N show 18-19 points?  A Cuebid would also show 19+ points.
        ["AQ6.KQJ97.AQ76.5", "2S", "1D 1S X P"],  # p131, h14
        ["J43.KJ97.AQ76.Q7", "2H", "1D 1S X P"],  # p131, h15

        ["KQJ6.AQ6.A7.QJ75", "2H", "1C 1H X P"],

        ["62.AQ876.KJ97.A8", "2H", "1D 1S X P"],  # p132, West
        ["KQ8.J9.Q8653.753", "X", "1D 1S"],  # p132, East
        ["A864.863.AQ.KT32", "2S", "1C 1D X 2D"],  # p132, West
        ["J97.52.KJ74.QJ74", "X", "1C 1D"],  # p132, East

        # Make sure that we prefer 1S when we have 5 of them:
        ["32.432.432.AKQJ2", "1S", "1C 1H"],
        ["32.432.432.AKQJ2", "1S", "1D 1H"],
        ["5432.2.5432.AKQJ", "X", "1C 1H"],
        ["5432.2.5432.AKQJ", "X", "1D 1H"],

        # Prefer mentioning the new suit directly when we have 5.
        ['Q832.QT.K4.AQT93', '2S', '1D 2H', 'N-S'],  # 2-f41c9d56243758ca09bae48fb3, W
        ['Q832.QT2.K4.AQT9', 'X', '1D 2H'],
        ['Q832.QT.AQT93.K4', '2H', '1D 1S'],
        ['Q832.QT2.AQT9.K4', 'X', '1D 1S'],

        ['A.AQ94.KJT95.Q53', '2D', 'P P P 1H 1S X P', 'Both'],  # 4-4ddd50827c9e21e4eae4881def, S needs to bid 2D in response to the negative double.

        # No need to search for minor fits when we already have a major fit.
        ['J854.A64.A94.QT7', '3H', 'P 1H 1S', 'E-W'],  # 3-85c71e2998bbdc4e9ff4a24d10, E
        ['52.A95.AT3.KT843', '3H', 'P P 1H 2C', 'E-W'],  # 16-e384a665c6ca37604d6ef9330d, W

        # Look for the possible major instead of supporting a minor:
        ['QJ875.KQ2.9542.9', 'X', '1C 2S', 'N-S'],  # 5-722868214ffeb9a3ef51407947, S

        # Showing a 6-card major is still higher priority than a minor.
        ['93.AQ43.9.AQT942', '2S', 'P 1S 2C X P', 'E-W'],  # 6-2c52fcca44f260dd251e67dae2, S
        ['Q43.AT93.KJ9854.', '2H', 'P 1H 1S X P'],  # 11-7ca9ad5e49f43af1fb76214080, W

        # We're too strong to limit-raise and have too many spades to negative double:
        ['Q2.A95.AT3.KT843', '2S', '1H 2C'],

        # When negative doubles apply, they're more descriptive than placement bids:
        ['K8732.J32.A.A942', 'X', '1H 2D', 'Both'],  # 4-5a96c9d60ac4cefae0359cc4cd, E

        # Seems reasonable to start with a negative double and go from there?
        ['8532.A854.A74.AK', 'X', 'P 1H 2S', 'Both'],  # 13-f34c952bc728b5d3914e62886f, W

        # Partner is bound to like one of our minors.  We've got the majority of the points anyway.
        ['AKJ953.Q7654.K.6', '3D', '1C 1S X 2S', 'E-W'],  # 3-6602e682a95e47c31d2f32477f, S

        # This hand does not want to play NT, despite having the points.
        ['KQJ754.AQ93..K84', '3D', 'P P 1C 2S X P', 'E-W'],  # 6-9f793fad48e7b484a64631324c, W

        # The lack of double earlier is questionable, but at least 3S shouldn't trigger an assertion:
        ['J432.AK32.AK32.2', '3S', '1C P 1S P 2S X P'],

        # We'd rather raise a major than rebid our minor.
        ['KQJ983.Q4.J.AK96', '2S', 'P 1C 1D X P', 'Both'],  # 10-21fa6afe513e343f7611d2094a, S
    ],

    "test_reopening_double": [ # Chap 17
        ["865.643.T4.87542", "2S", "1D 2C P P X P"],  # p135, Partner 1
        ["8743.Q9863.T4.87", "2D", "1D 2C P P X P"],  # p135, Partner 2
        ["AQT753.843.Q2.42", "P", "1D 2C P P X P"],  # p135, Partner 3

        ["AK6.93.A42.K7652", "X", "P P 1S 2D P P"],  # p136, West
        ["QJ3.KJ876.863.QT", "P", "P P 1S 2D P P X P"],  # p136, East

        ["643.KT94.AKJ53.7", "P", "P 1S 2H P P X P"],  # p137, West
        ["KQ5.QJ3.2.AJ6543", "X", "P 1S 2H P P"],  # p137, East

        ["Q93.5.AT93.AKJ53", "X", "P 1S 2D P P"],  # p138, West
        ["KT6.AQJ74.874.T2", "P", "P 1S 2D P P X P"],  # p138, East

        ['AJ75.A92.KT2.AK3', '2N', '1C 1D P P', 'Both'],  # 10-f912dc5ece6e9682f41b48f085, E

        ['3.AK954.A985.AK5', 'P', 'P 1D 1H P P X P 1S P', 'E-W'],  # 6-255c53f6b385a123a7f81b1f0a, S cannot say 2H once East has mentioned hearts and should Double and then pass.

        # A double seems more descriptive here?  Unclear if this is "reopening"?
        ['KT86.QT87.K.A843', 'X', '1D P P 1H', 'N-S'],  # 12-51ced3125f33a24691baf8b44b, W
        ['J762.KQ86.AK54.A', 'X', '1D P P 1S', 'Both'],  # 10-7850d282d1ad6f5fead708ce81, E

        # This is our hand.  Don't need to try and penalize them, or?
        ['.KQ874.KQJ7.AKQ2', '3H', '1D 2C P P', 'Both'],  # 7-3757fc0e4a32bd72d2ae41506a, S
    ],

    "test_balancing": [ # Balancing (Chap 18)
        # Balancing Overcalls (p140)
        ["974.J85.AJT872.9", "2H", "1S P P"],  # p140, h1
        ["9.KQ5.AKT872.J65", "2H", "1C P P"],  # p140, h2
        ["KJ8.A74.JT874.86", "2H", "1D P 2D P P"],  # p140, h3
        ["Q98.K74.43.QJ874", "2S", "1H P 2H P P"],  # p140, h4
        ["QJ98.84.43.KQT87", "1S", "1H P P"],  # p140, h5
        ["K98.K974.QJ7.987", "P", "1H P 2H P P"],  # p140, h6

        # Balancing Notrump
        ["JT43.KJ4.KT8.KQ6", "1N", "1S P P"],  # p141, You

        # Systems are on.  Does stayman require 11+?
        ["JT4.K4.KJT8.K864", "2C", "1S P P 1N P"],
        # 2N raise definitely requires 11.
        ["KJT8.K864.K4.JT4", "2N", "1S P P 1N P"],

        # Balancing Doubles
        ["42.AJ3.K954.QT87", "X", "1C P P"],  # p142, h7
        ["42.AJ3.K954.QT87", "P", "1C"],  # p142, h7-alt
        ["QT752.73.A94.AT6", "X", "1D P P"],  # p142, h8
        ["QT752.73.A94.AT6", "P", "1D"],  # p142, h8-alt
        ["KT6.QT87.84.AT84", "X", "1H P 2H P P"],  # p142, h9
        ["K87.AJ76.65.Q863", "X", "1H P P"],  # p142, h10

        # Balancing with strong hands
        ["AKQ5.84.72.AQJ93", "X", "1H P P"],  # p142, h11
        ["AKQ5.84.72.AQJ93", "1S", "1H"],  # p142, h11-alt
        ["K92.QJT7.KQ4.AJ7", "X", "1H P P"],  # p142, h12
        ["K92.QJT7.KQ4.AJ7", "2N", "1H P P X P 2C P"],  # p142, h12 (continuation)

        # Balancing Michaels
        ["QJ875.A.KT9854.9", "2S", "1S P P"],  # p142, h13
        ['.J.KQT762.AKT932', '2D', '1D P P', 'E-W'],  # 6-da7b9d695ae253d0f30827e070, N

        # When not to balance
        ["4.QJ96.KQ65.Q865", "P", "1H P P"],  # p142, h14
        ["J87.T9652.A43.98", "P", "1C P P"],  # p142, h15

        # Responding to a balancing overcall
        ["K83.K95.K54.QT75", "2S", "1C P P 1S P"],  # p144, h16
        ["Q973.42.AT95.K87", "2S", "1C P P 1S P"],  # p144, h17
        ["QJ62.K32.A4.K843", "3S", "1C P P 1S P"],  # p144, h18
        # FIXME: Need tests for NT responses (none given in the book).

        # Responding to a balancing double
        ["AJ3.864.JT4.KQ73", "2S", "1D P P X P"],  # p145, h19
        ["AJ3.864.JT4.K873", "1S", "1D P P X P"],  # modified h19
        ["543.AQT43.KT4.K6", "P", "1D P P X P"],  # p145, h20

        # Responding to a balancing 1NT -- no tests provided. :(
        # Systems are on, just require more points.
        ["AQ3.T64.KT43.Q64", "2C", "1D P P 1N P"],
        ["AQ3.T643.KT4.Q64", "2N", "1D P P 1N P"],
    ],

    "test_slam_biding": [
        # FIXME: The slam bidding chapter has no hands, but does have more sequences we could test.

        # 4NT Quantitative (invitational)
        ["QT64.AK8.KT6.A62", "4N", "1N P"],  # p156, East
        ["KJ.QJT9.A873.KQ3", "6N", "1N P 4N P"], # p156, West, # FIXME: Why is 16 the "top end" of the 15-17 range?
        ["JT64.AK8.KQ6.A62", "4N", "1N P"],  # p156, East
        ["KQ.QJT9.A87.QJ73", "P", "1N P 4N P"], # p156, West

        # 5H/5S functions like 4NT, inviting to small slam based on quality of trump holding.
        [".AKQ.QT76432.AKQ", "5H", "1H P 3H P"],
        ["AKQ.JT98.J985.62", "P", "1H P 3H P 5H P"],  # Not good enough for slam.

        [".AKQ.KJ76432.AKQ", "5H", "2C P 2N P 3H P 4H P"], # Another way to bid the hand.
        ["QJT.AK98.J985.62", "6H", "2C P 2N P 3H P 4H P 5H P"],  # Slamtastic?

        # Grand Slam Force
        [".AQ753.AJ5.K8762", "6S", "1S P 5N P"], # p157
        ["AKQJT987...QJT43", "P", "1S P 5N P 6S P"], # p157
        # If we had 2o3 in trump we would have gone to grand:
        [".AQ753.J5.AK8762", "7S", "1S P 5N P"],

        # FIXME: Missing tests for p158+

        ["A63.J43.AKQJT.A2", "5S", "1H P 2N P 3H P 4N P"], # 4N is blackwood after Jacoby2N
    ],

    "test_misc_hands_from_play": [
        ["A852.K6.T3.A8732", "2C", "1S P 1N P"], # deal 2055120848382729270948723852852, N interpreted my 1N as an opening and bid 2H. (like h5, p52)
        ["KQ6.Q965.K5.AQ98", "2S", "P 1N P 2C P"], # deal 5671897354712543810227745124780, E failed to reply to stayman.
        # deal 357243086480349253440501420960, N opened 1N with a singleton (missing a good spade fit)
        ["732.Q.AJ.AKJ9843", "1S"],
        ["T3.A7.KQT86.KJ63", "4H", "1H P 2N P"], # S from 8791080045553853812852250533176
        # deal 13166359304130342084190377474345, N underbid using length_points instead of support_points (Adam was sad)
        ["AQJ5.QT42.74.T52", "3S", "1S P"],
        # deal 17629222268064766858640312666151, W jumped straight to 3NT after 1H, possibly missing the 4-4 spade fit.
        ["A2.T752.KQJ.AQ72", "1S", "1H P"],
        # deal 8519752870456625075160666360030
        ["KQ94.J976.KQ7.A2", "4H", "1N P 2D P 2H P 3N P"],  # E should transfer to 2H, then bid 4H, seeing a heart fit.
        ["A53.A8.J9854.J64", "3N", "1N P 2D P 2H P"],  # W should bid 3N to offer E a choice between 3N and 4H.
        # deal 12654421273047901180661788961394 - 6NT slam for E-W.  E didn't know how to respond after 1N
        # With only 15 hcp. We're supposed to bid 2C, 3C for possible slam interest (p14).
        ["AKQT5.Q865.875.K", "2C", "1N P"],
        ["J94.AK9.A9.QJ932", "3N", "1N P 2C P 2S P 3C P"],  # West's hand is a minimum and plays best in NT.
        # It's unclear if the auction should continue from here, however if we pass all of the above, I'll be ecstatic.
        # deal 3428385259717852034512334730768, N failed to bid 3N with 19 hcp.
        ["AKQ532.K8.K73.A9", "3N", "P 1C P 1D P"], # This is most like h21 (p54), which suggests 3N.
        ["AKJT94.AJ65.8.T6", "P", "1D", "None"], # deal 12948369311012751542781072470235, p99 be cautious about overcalling for 4 cards in opponent's suit.
        # deal 12948369311012751542781072470235, W bid 2D (opponents's suit with only 5 points, and wrong shape for michaels)
        ["852.943.KJ64.J85", "P", "1D 2C X"],
        ["Q9754.AJ8.A9653.", "4H", "1H P 3H P"], # deal 16395022320723557606872785241182, E failed to bid game after invitational 3H from W.
        ["AQ765.AQ8.J3.K83", "P", "P P 1H 2C 3H P 4H", "N-S"],  # deal 15672814881672178555734100647993, N should overcall 2C and then shut up.
        ["4.A92.AKT632.J62", "1H", "P 1C", "N-S"],  # deal 13780264151805956424559071595032, E should overcall 1H
        ["KJ87.53.94.AKJT3", "1S", "1C P 1D", "Both"],  # deal 7084727285179457149524958910088, E should overcall 1S
        ["A93.Q762.K832.J3", "P", "1D P 1H P 1S P 2N P 3N P", "E-W"],  # deal 13032830395998601871443699251555, N I believe N's 2NT was correct (p70)
        ["864.A6.QJ65.K987", "4H", "P P P 1N P 2C P 2H P", "None"],  # deal 9606125883933381651464004418488, W failed to raise E to game after he showed 4 hearts
        ["J2.AQ8642.J72.KQ", "2D", "P 1D P 1H P"], # deal 17104155942037401012949293200001, exception while E was trying to bid.
        ["6.AKJ75.KJT86.A4", "P", "1H P 2N P 4D P 4H P"], # deal 2137828841254613144319938747574, exception interpreting Jacoby 2N (south's bid is wrong, but useful as a test)
        ["KQT4.AT96.632.T8", "2C", "1C P 1D P 1S P", "Both"],  # deal 14821420111709134787520015678345, N should retreat to clubs instead of NT.
        ["KQ4.KT4.AJ32.954", "3N", "P 1C P 1H P 1N P", "None"],  # deal 19769130892564304556643507165641, N needs a spade stopper to go to 2N? (south shouldn't have opened, oops!)
        ["KQT.95.AK74.AJ53", "4H", "P P P 1N P 2C P 2H P 3H P", "None"],  # deal 9606125883933381651464004418488, East should bid game directly, seeing 25-27 points and 8 hearts.
        ["AKQ6.KQT.T4.QJ96", "P", "P 1N P 2C P 2S P 3N P", "Both"],  # deal 7666900753141668445629354337434, N previously was bidding 4N!
        ["QT8.AQ95.KJ532.4", "P", "1H P 1S 2D", "E-W"],  # deal 2713109889156458295693804380142, E should pass.
        ['432.AT.T95.AKT87', '1S', 'P P 1D P P', 'Both'],  # deal 12734075338630212034897921725930, S should overcall 1S.
        ['AK532.T63.86.AT9', '3N', 'P 1N P'],  # deal 9773241304968681226215328063605, E should bid game.
        ['Q98.KQT2.75.AJ92', '2S', 'P P 1D P 1S P', 'Both'],  # deal 3211822235255751313198808697687, N should prefer to support spades instead of 2NT
        ['KJT7.764.32.KQT8', 'P', 'P P 1D P 1S P 2S P', 'Both'],  # deal 3211822235255751313198808697687, S should pass, having found an 8card fit with no game chances.
        ['K9.AJT86.AKQT4.9', '2H', '1S P'],  # deal 15516513128457595171295904948924, E should mention his hearts first.
        ['Q76.Q92.7.AKQT64', '3S', 'P P 1D 1S 2C 2S 3C', 'N-S'],  # deal 172713781760825487196521615525, north should not bid NT after finding a major fit!
        ['54.AJ4.T8652.J97', '2S', 'P P 1D 1S 1N', 'N-S'],  # 2-5a0771ce7f386b689b7d44b880, S should support N's overcalled spades, assuming 5.
        ['AJ9.T8763.AKJ3.8', 'P', 'P P 1D 1S 1N 2S', 'N-S'],  # 2-5a0771ce7f386b689b7d44b880, W should probably just pass.  Takeout double is unlikely to help.
        ['QJ732.AQ97.96.J5', '3N', 'P 1N P', 'Both'],  # deal 1553211445300727281165243559583, W failed to jump to game
        ['KT76.98.K8754.94', 'P', 'P 1H X 3H P 4H X P', 'N-S'],  # deal 8382037091299794628457966133495, N bid 4N after S's game double!
        ['KQ742.T.QT542.T2', 'P', 'P 1C P 1H P 2H P', 'N-S'],  # deal 983851022516199954010479458001, E should mention delayed club support, but only once.
        ['KJ9.AK832.T987.5', '2D', '1S P 1N', 'E-W'],  # Slightly modified W from deal 8087525203290005445964033020522
        ['74.AQ752.KJ5.J85', '2C', 'P P P 1C 1H 1S', 'N-S'],  # 15-10222479319156695433645509043224-W:NS: E should have competed for part score.
        ['87.754.K54.AK754', 'P', 'P P 1N P 2C P 2D P 2N P 3N', 'N-S'],  # deal 1062232275178304430354351375273, N shouldn't overcall, unlikely to find a fit.
        ['A642.53.973.AT98', 'P', 'P 1D P 1S P 1N P', 'Both'],  # deal 4517066310038174380006179757260, N was incorrectly bidding 2N
        ['A8.AJ854.K7.AT62', '1S', '1D P 1H P', 'E-W'],  # deal 2951009855043816914734430995830, N needs to mention his 4 card spade suit.
        ['Q65.KJ853.A.Q952', '1S', '1H P'],  # board 14-7826729667235676373557841919005-S:NO:, N should mention his 4 spades before his 5-diamonds (p42)
        ['KJ52.K92.AK84.J5', 'P', '1D 1N P 2C P 2H P 3H P'],  # 11-14607544081589328645359823665724, NT overcall and stayman.
        ['K4.AKQJ94.87.A96', '6N', '1D P 2H P'],  # Misentered version of p54, h21
        ['K67.AKT92.J975.A', '1N', '1D P 1S P'],  # 16-3454156737664725749576366666997, too weak to reverse and no other good bid.
        ['K67.2.J975.AT942', 'X', '1C 1D'],  # Negative doubles after 1C 1D can be used to show 4+/4+ in the majors.
        ['AJ.AQ2.KJ2.AT875', '4S', 'P P 1S P 3S P', 'Both'],  # deal 1990779642997181941127458223871, N failed to accept game with 19 points.
        ['A2.K94.KQ7643.94', '2H', '1H P 2C P', 'E-W'],  # deal 6804290325301182951483855664194, S was jump-rebidding when he shouldn't
        ['75.J5.82.AKQJ753', '3S', '1H P 2C', 'E-W'],  # deal 6804290325301182951483855664194, E should mention his spades at first opportunity
        ['AKQ643.KQ76.9.72', 'P', 'P P 1C P 1S P 2C P 3C P', 'Both'],  # deal 6377263314736776685553120514792, S
        ['AK83.8652.8.AJ73', '3N', '1D P 1S P 1N P 2N P 3S P', 'E-W'],  # deal 1979684472506296751065025333154, N should be optimistic and place the contract in 3N
        ['QJ973.A8742.A.75', 'P', 'P P P'],  # deal 7975802526261699718647409200414, W should P without a rule of 15 opening
        ['A64.J63.Q953.Q54', 'P', 'P P P 1N P 2C P 2S P 2N P 3N P', 'Both'],  # deal 1940213521505485420902055992864, S should not bid stayman again
        ['A7.K.QT6.KJ98543', '4S', '1C P 1S P 1N P', 'N-S'],  # deal 10835457922689972148224318394842, N should count his partner for at least one spade and bid 4 directly.
        ['J7542.A9.J9843.7', '3H', '1S 1N 2S P P X P'],  # deal 2516264305691961020389553592486, a complex auction where N/S appear to miss their game
        ['AJ93.T874.K3.Q75', 'P', 'P 1C P 1H P 1N P 4H', 'Both'],  # deal 17957643975053861560971898729953, N should jump straight to game, knowing his partner has at least 2 hearts.
        ['AKQ8.KJ7.T8.AQ87', '4C', '1H P 1S P 2D P', 'N-S'],  # deal 16286079713409328537740982237218, W can bid 1S, even with 19+ points.
        ['K9.J962.62.AT863', '2D', 'P P 1S X P'],  # deal 1828153217228812714095889759725, N should respond 2D, even though he is longest in the opponents' suit.
        ['A9863.QJT7.8.KJ6', '1N', 'P 1C P 1H P', 'E-W'],  # deal 12456243253839719652904629983622, E can bid 1N despite having only one heart.
        ['KJ3.T96.QT865.J4', '2D', '1D P 1H P 2C P'],  # deal 7051096585500849502473608601267, N is assuming that by mentioning Diamonds first South has more of them.  He happens to be right.
        ['Q632.JT52.743.86', 'P', '1S 2S P 2N P 3C P', 'N-S'],  # deal 6177852048991998477340369815114, S should ask for North to name his Minor, planning to pass him.
        ['Q632.JT52.743.86', 'P', '1S 2S P 2N P 3D P', 'N-S'],  # modified from deal 6177852048991998477340369815114, S should ask for North to name his Minor, planning to pass him.
        ['K654.AQ.864.T653', '4H', '2D X P 3C P 3H P', 'N-S'],  # deal 13247511199031202103262541969417, N should bid game seeing 26 points and an 8-card fit.
        ['85.T.KJ43.KQ9752', '3H', '1D 2S P 2N P'],  # deal 10261368563172950620196330721081, N should show his protected K of hearts as his "feature".
        ['KQJT3.864.AQ9.AT', '4S', '1D 2S P 2N P 3H P'],  # deal 10261368563172950620196330721081, S should bid game, seeing N has a maximum.
        ['KQJT3.864.AQ9.AT', '4S', '1D 2S P 2N P 3N P'],  # modified deal 10261368563172950620196330721081, S should bid game, seeing N has a maximum.
        ['QT8.KQ632.86.T97', '1N', 'P P 1C P 1D P 1H P', 'N-S'],  # deal 18461602223397807530713780374231, N should bid 1D.  An earlier version of the bidder failed to.
        ['JT87.A732..KQJ72', '3S', '1D 1S P 2D P'],  # deal 15141057107213075875501235469840, W should overcall 1S rather than pass.
        ['AJT95.AK4.K93.K6', '1N', '1S', 'Both'],  # deal 16428150251578352755575396243774, N could big-hand double if we use length-points for big-hand doubles?
        ['AQJT9.AQT3.5.T52', '5N', '2S X P 3C P 3H P', 'E-W'],  # deal 5046897236076953230543124332887, S shouldn't pass.  Our current behavior of 5N is better than nothing (they make 6N cold).
        ['KQ986.K.AK7.J942', 'P', '1N P P', 'Both'],  # deal 14701784778261743532608945607084, E likely has to pass, but mostly the bidder shouldn't crash.
        ['K83.Q.K75432.QJ6', 'P', '1D P 1H P 1S P 3H P 3N P'],  # deal c5e1e879669c60049dcf78fe0a, N shouldn't jump rebid his suit again
        ['KQ4.KJ.K84.KQ973', '6N', 'P 1N P 2C P 2S P 5N P', 'Both'],  # deal c60ab53c02077a6c78df6a7497, E should accept quantitative 5N
        ['QJT4.AQJ.765.AQJ', '6N', '1N P 4N P', 'Both'],  # deal a3a7019de7e087c077a99e750c, N should accept quantitative 4N
        ['AQ6.K643.65.KQ96', '4S', '1C 1D 1S P 2S P'],  # deal 17b339ba635583e8dc4d1e18e8, S should bid 1S after 1D, showing only 4 spades
        ['AJT8.J8.K52.KJ83', 'P', 'P 1C 1D 3C 3D', 'E-W'],  # deal 3438a48dc639f9e711639f648b, S shouldn't bid 3N without a stopper
        ['AQT854.7.AJ98.J3', '2C', 'P P 1C P 1S P', 'N-S'],  # deal d0f2122f72b5d7a70cb129592b, N can rebid clubs even with four hearts
        ['A8763.432.K6.763', 'P', '1S 2S P 2N P 3D P', 'N-S'],  # 2-cd03e500ebb695a1ebc92c3765, N previously was bidding 3S as "raise response" over michaels.
        ['5.AJT9.Q85.AQ875', '3D', 'P P 1S P 2D P', 'N-S'],  # 5-7ecf177441ab206fbc8758a522, S shouldn't rebid his own suit as that would deny 4 diamonds?
        ['AT9.Q97652..AJ64', 'P', '1D P 1S P 2S P 4S P', 'E-W'],  # 3-4d36b4a4a8b2f5c53d51eef082, S shouldn't rebid his 6 diamonds as that would deny 4 spades.
        ['A742.QJ765.Q4.Q4', 'P', 'P 1D P 2C P 3C P 3N P', 'E-W'],  # 6-99240cb7a9da01b705bce733e5, S shouldn't rebid his diamonds as that would deny 4 clubs.
        ['A642.AQJ42..K986', '3N', '1D X 1H P 1S P 2N P', 'E-W'],  # 6-767cfa51c085dea3803eb1d4a6, E should be 1S to show his 4 spades
        ['JT873.K5.AK72.74', 'P', '1D X 1H P 1S P 2N P 3N P', 'E-W'],  # 6-767cfa51c085dea3803eb1d4a6, W should bid 2N since 5 clubs is definitely a club stopper.
        ['AQT972.64.T6.K86', '2C', 'P P 1H', 'Both'],  # 10-25483338c6b67fe361ed9849d2, N should overcall 2C with 6 clubs though he only has 9 hcp.
        ['432.AKQJ.432.432', '1D', '1C'],  # Make sure 4-card overcalls work.
        ['KQT8.AK7432.9.K3', 'P', '1D 1H 2C 4H', 'Both'],  # 10-8fe7659526cf50831bb870a387, E should not bid 7D as a DoubleJumpRebid by opener!
        ['AK.K83.QJT76.986', '4D', '3D P'],  # 1-d35c1698320c817afa9d76e837, S should extend the preempt to 4D.
        ['AJ64.Q962.T7.983', 'P', '1N P'],  # 1-48bd61a524923ffe39119de83c, S should pass, 2N shows 8-9 high card points.
        ['3.KQ952.T732.A84', 'P', 'P 1H P 3H P 4H P', 'N-S'],  # 12-255d1f6f97828ac6cb01e12cf6, S should invite to game with 12 support points.
        ["T954.952.T863.82", "P", "2C P 2D P 2S P 3C P P"], # Turbo-pass the whole way down.
        ['J92.AKQ5.6.AKJ52', '3D', '1S P 2H P'],  # Constructed hand to show a possible 3D bid over 1S-2H.
        ['AQ8.532.AT985.96', '3N', '1S P 2H P 3D P'],  # N has a club stopper and should just bid 3N
        ['876.A3.AT9852.Q6', '3H', '1S P 2H P 3D P'],  # No club stopper, but 6 hearts warrants a rebid.
        ['876.A32.AT985.Q6', '3N', '1S P 2H P 3D P'],  # Despite having no club stopper, 3N is the best option?
        ['AQ852.KQ7.7652.J', 'P', 'P 1C 1H 1S P 1N P 2S P'],  # 14-b658499f5bc29bea047f047383, South's call is hard here.  He has no Heart stopper, but 2C would show 6-clubs,  He just hopes 1N won't go too badly.
        ['876.432.K985.876', '3C', '2C P 2D P 2N P'],  # Stayman should only require 3+ hcp and a 4-card suit over 2C->2N.
        ['J64.K7.AKQ94.AQ9', 'P', 'P P P 1H P 1S P 2N P 3N P'],  # 1-1ee635912d26c8e078fd664e33, W should jump to 2N, denying 4 spades.
        ['AKQJT4.2.KT2.J98', '5C', 'P 1D 2S 3C P 3D P', 'E-W'],  # 6-d1f7000aa6b6639e51496f833f, N needs to mention his clubs, even at the 3 level, then could bid 5C offering a game choice?
        ['.AQ986543.A74.74', '3D', 'P 1D 2S 3C P', 'E-W'],  # 6-d1f7000aa6b6639e51496f833f, S is forced to bid and should use his 3D minimum rebid.
        ['JT.73.KQ76542.86', 'P', 'P 1S 2D'],  # 1-8061f64e2c962eff60f4477962, W Jump-overcalls do not apply if partner bid (can't say 3H).
        ['J.QJ.KQ854.AQJ53', 'P', 'P 1S P 1N P 2H P 2S P', 'Both'],  # 4-9f76c5e69bb0e70b260e31d508, N should pass after South's sign-off.
        ['J2.AQ84.T9432.J7', '2N', 'P P 1C 1N P 2D P 2H P', 'E-W'],  # 6-bc55e0d60e426ab7e8704c97bc, S should invite to game with 2N.
        ['AK2.AK8.874.QT42', '1N', '1C P 1S', 'Both'],  # Indirect 1NT overcalls should be possible.
        ['6.KQJ985432..AQ8', '2D', '1H P 1S', 'N-S'],  # 12-cd97772a869a8f433334c461e6, S should be able to make an indirect overcall of 2D.
        ['AK7432.543.QJ9.5', 'X', '1S 2C 2S P P', 'E-W'],  # 16-014994301ed667fa883de39deb, N should balancing double to protect his partner.
        ['K42.AJT7.QT8.T63', '2N', 'P 1N P', 'E-W'],  # 6-13bfb4a5d2c1859b113b1cac6e, N should only bid 2N, discounting 1 point for having a flat hand.
        ['AT6.K82.A64.AQ87', 'P', 'P 1N P 2N P', 'E-W'],  # 6-13bfb4a5d2c1859b113b1cac6e, S should pass the game invitation, discounting 1 point for having a flat hand.
        ['KT54.KJ73.KJT6.Q', '2H', '1C 2C P'],  # 8-7a03b6d95bd9b30b1a605c43e3, S should pick a major.  Unclear if this should be 2H or 3H.
        ['J42.AT9.987632.5', '4H', '1D 1H 1S'],  # 8-8b54e731fdaf2a0aa43149f057, S should only jump to 4H, despite having 6 hearts.
        ['AK742.A.T972.Q63', '4S', '1C P 1S P 1N P 3S P', 'N-S'],  # 15-8b6d469cdfcd684e68f7867020, S should rebid with 1N, having no better bid.
        ['732.A62.KQ964.J7', '2H', 'P P 1D 1S P', 'E-W'],  # 3-f239907a319831ecb4f162dad5, W should mention his hearts in response to his partner's overcall.
        ['5.9643.K7542.QJ5', 'P', '1N P 2D P 2H P', 'N-S'],  # 5-12f05d5a67b30ba64d63c933ac, S should never plan garbage stayman when he could escape tranfer instead.
        ['AKQ852.K8.T.KJ93', '4S', '1S P 2N P 3H P', 'N-S'],  # 15-14d3b03b685a1ff7937625e222, N should bid Jacoby2N and consider slam (they make 6S).
        ['J5.KJ7.AKQ74.963', '4H', '1H X 2N P', 'Both'],  # 13-f8b7c66e93521b3cab0114539e, N should jump to game after Jordan2N.
        ['AT8.J965.K85.Q97', '3H', '1D 2N P', 'N-S'],  # 2-9ba21f160f1157893a8bf532c7, N should chose hearts over clubs, assuming 5 in each.
        ['A96432.5.KJ8.AQJ', '2C', 'P 1D', 'N-S'],  # 5-a89274b18744111cbee73f3da6, S with 6 clubs and 15 points seems we can compete for a part score.  Takeout double is wrong shape (if he has a 5 card major he'll mention it).
        ['.AQ964.J9752.Q75', '2N', 'P 1N P 2D P 2H P', 'Both'],  # 4-cd0570ce678e29622ef07997e1, S despite having nice looking diamonds, with only 9hcp, bididng 3D could end up in 3N with only 24 points.  Pass.
        ['AQ72.AT82.32.K74', 'P', 'P 1D P 1S P 2C P 2D P', 'Both'],  # 13-681ac45cad9ed503e22f1f7c86, E doesn't have enough strength to show delayed support after partner sign-off.
        ['84.KT9765.4.A763', 'X', '1H 2C', 'Both'],  # 10-8e9ca498fef0d5e42468e3c553, W should arguably negative double, despite having only 7hcp.
        ['Q62.T7.KT982.A75', '1N', 'P P 1D P 1H P 1S P', 'E-W'],  # 9-2f2e91795346a1f5038fa137e8, N should show his minimum and lack of fit with 1N.
        ['T973.AKQ3.Q.KQ43', '2N', 'P P 1D P 1H P 1S P 1N P', 'E-W'],  # 9-2f2e91795346a1f5038fa137e8, S should invite to game with 16 points.
        ['K7.Q76.AJT84.K98', '3N', 'P 1C P 1H P 1S P', 'N-S'],  # 15-3090bdf896a9cc4c75878a97f4, E should bid 3N, counting Qxx as a stopper in unbid diamonds.
        ['KQ8.K62.Q432.AK8', '3N', 'P 1S P', 'E-W'],  # 6-dd73a0c5859e201b572fbd8ae0, N should jump to 3N.  Possibly missing a spade slam, but anything else seems a lie (maybe 2C first?).
        ['AKT964.975.7.965', '5D', '2C P 3C P 4N P'],  # 11-d1181429212aeffcddeb50d1ba, N cannot pass blackwood.
        ['AK.AK54.98.KQJ76', '2N', '2H P', 'E-W'],  # 6-02a6a3c7e285f146f4154bc6fe, W should make a feature request response to East's preempt.
        ['AKQ5.KJ93.AQ97.4', 'X', '1S X 2S P P', 'E-W'],  # 3-83852fec64ddc46770ed7a290a, W should probably double again and certainly can't bid 2N.
        ['Q4.K32.QJT8.AK94', '3S', 'P P P 1N P 2C P 2H P 2N P', 'E-W'],  # 9-1d8a6e7c8442d68adfc1724e4f, W should bid 3S to show his 4 spades.
        ['KJ64.9.K6.KT7542', 'P', '1S P 2C P 3C P 3S P 4S P', 'Both'],  # 10-acd53782a0e0994e20b37ddb5d, W shouldn't bid 5C over partner's 4S.
        ['AQ7.AJT9762.5.Q4', 'P', 'P 1H P 2D P 2H P 3D P 3N P'],  # 8-fd63c9a069ab206373306d5f64, S should rebid his diamonds at the 3 level, lacking anything better to do.
        ['QT62.Q8.J94.KT76', '3H', 'P P P 1H P 2H P 3D P', 'N-S'],  # 12-351b317a7c78e636489b742ce2, N should retreat to 3H being one point short of game.
        ['J83.AQJ8.72.Q763', '2D', 'P P 1D P 1S P 1N P', 'E-W'],  # 6-1cc61a8fe185d429cece79639c, E does not need to jump to 3D, 2D is sufficient.
        ['AK.K8.AKT762.953', '3H', 'P P 1H P 2C P'],  # 11-9d66e43bb47a11b0d18113f2eb, N should jump to 3H, not 4H.
        ['982.AK4.Q8.AJT53', 'P', 'P P 1S 1N P 2D'],  # 1-957a7f12330ca57485bd883eb2, S should not rebid his spades.
        ['T6543.2.JT6432.2', 'P', 'P P 1S 1N P 2D 2S P P'],  # 1-957a7f12330ca57485bd883eb2, E should just pass if partner fails to accept the transfer.
        ['6.A74.Q96532.K85', '4H', 'P P 1S 1N P 2D P 3D P', 'N-S'],  # 12-6f1de5b8e3ea40424a3b634771, N should do something reasonable, even if partner doesn't accept our transfer.
        ['AT62.J7652.J5.96', '3D', '1S X 2S P P X P', 'E-W'],  # 6-351a160a02f2b98ffcbb747165, N should recognize partner's second double as takeout and bid.
        ['T8.KJ7.Q74.Q8654', '2S', 'P P P 1D P 2C P 2D P P X P', 'E-W'],  # 9-a7523e7fa171372ce91e40858e, N needs to recognize this double as for takeout.
        ['96.87.J653.AQT94', '1S', 'P P 1D P'],  # 1-f53c6dbd60dfa84294f98da048, N should mention his spades before his hearts.
        ['A5.AK98765.5.KJ7', '3S', 'P 1D P 1S P 2D P 2N P', 'N-S'],  # 2-d2534c9caa9da7e35f130580bb, S should give delayed support for spades.
        ['AQ72.AKJ53.A82.5', 'P', 'P 1D 1S 1N P 2C P 2D P', 'E-W'],  # 16-3fcad21139a1019d3eb3a35e59, N should know how to pass.
        ['A54.QT5.J743.QJ7', 'P', 'P P 1N P 2C P 2S P 2N P 3N P', 'E-W'],  # 19-5ac1f4b495ee32b6d2f01d93a0, S should just pass, slam is remote.
        ['J.AQ972.T5.JT964', 'P', '1H 2H 3C 4S P', 'E-W'],  # 6-f34c2fec19b6e76d19d4220a85, S should pass after partner jumps to 4S.
        ['83.KQ732.Q2.AKJ9', '2D', 'P 1C 1D P P 1H 1S P P X', 'E-W'],  # 9-2d0b506bd9f29b0d71b735388a, S should be able to bid after making a previously invalid bid?
        ['94.932.QT95.K872', 'P', '2C P P', 'E-W'],  # 9-9c67513c92c605b9bcc391faac, If south fails to respond to partner's artificial club, just leave them there.
        ['A853.K.K2.KJT943', '3S', 'P 1S P 2D P', 'Both'],  # 26-227bdd84f4c788f0552da7ca98, S should use length points for computing his rebid?
        ['9.AKQT63.AQ.K865', 'X', '2H X 4H P P', 'E-W'],  # 6-c11e74c92722addf159bca23d8, S can't bid game w/o his partner, but he can double for penalties.
        ['875.K8752.Q6.986', 'P', '1C X P 1D 1S 2N P', 'Both'],  # 7-e916fad3458f72c42078e9942f, E should continue on to game.
        ['AJ6532.T73.J6.86', '3D', '1C 2N P', 'E-W'],  # 16-a2b5ef987820733902df5e654c, S should prefer 3D as it is a better fit.
        ['8.Q5.K854.QJ7532', '1S', 'P 1C P', 'N-S'],  # 2-7ea3de962fd8750d2788231b05, N should mention spades first.
        ['.K54.A9842.Q9543', '2N', 'P P 1D P 1S P 2C P', 'E-W'],  # 3-45cdcc468c0489bcafdba9db61, S should mention spades first, then invite to NT game.
        ['A72.QJ65.AJ.K875', '3N', '1N P 2C P 2D P'],  # 14-e87a95c4f12f51a603ae4cf61c, W shouldn't miss game.  Slam is remote with max 32 points.
        ['J98652.942.T.AKQ', '2S', 'P 1D 2D P'],  # 14-61451c9daa40eae3f7202ff2d5, E should pick spades.
        ['.T743.AKJ63.AQJ4', 'P', 'P 1H 4C P P', 'E-W'],  # 9-88eeaa25341e0df429d41bf35d, E should not double the 4-clubs preempt w/o more values?
        ['Q5.962.AKQ65.AQ2', '4S', '1N P 2H P 2S P 2N P', 'Both'],  # 13-58e7e18d893db7c3670069eac4, N should prefer 4S over 3N.
        ['AJ532.KJT7..AQJ9', '1S', 'P P P 1C P 1H P', 'E-W'],  # 16-a27c2c91f869bd0343515df8ae, S should bid 1S, not 2D.
        ['KT94.83.AT9654.T', 'P', 'P P P 1C P 1H P 1S P 2H P 2N P', 'E-W'],  # 16-a27c2c91f869bd0343515df8ae, N cannot rebid hearts again w/o 7.
        ['AQ73.AT6.QJ.QJ63', 'P', '1H P 2H X P 3C P'],  # 11-93d3c46a1398dc2bb16a41cf5e, E passes after his takeout double, showing < 17 hcp.
        ["K83.54.8632.A643", "3C", "1S P 2H X P"],  # Responding to a two-suited takeout double, have to pick the lesser of evils.
        ['K5.J86532.K6.AJ8', 'P', 'P P P 1D P 1S P', 'E-W'],  # 3-8da8bd165934e3c70a93c0da7d, W is already a passed hand, game is remote.
        ['AKQ76..AT32.AT84', 'X', 'P P 1N', 'N-S'],  # 2-b90e90257d67b07a61f38788dc, N needs to begin with a big-hand double.
        ['AT6.KJ864.A4.A42', 'X', 'P 2H', 'E-W'],  # 6-51d4cadbb32cc5caa28fb06553, W should takeout double.
        ['962.863.KQJ7.KJ7', '2N', 'P P 1D 1S X P 2C P', 'N-S'],  # 5-1f28db93c85ba5589c077a3933, N should probably bid 2N to show his invitational hand.  Or would that show 17+?
        ['AKJ.T53.KQ65.KJ2', '3N', 'P 1N P 2C P 2H P 2N P', 'Both'],  # 10-cddc6288b36f35691da2c051bb, S should bid 3N with 17 hcp?  Even if flat?
        ['AK.72.KT942.AQT5', '1H', 'P 1C', 'N-S'], # S should bid 1H
        ['AKT4.AT.A82.J876', '1N', '1C P P', 'E-W'],  # 9-9e00d3d9a9b93e48d91d07f2d8, W should overcall 1N (or maybe big-hand double?)
        ['QJ86.K7.AKT53.T6', '2H', '1H P 2D P', 'E-W'], # Not enough points to say 3C, but we can't pass partner.
    ],
}
