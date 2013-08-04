module "ScoreCalculator"


expectScore = (expectedScore, contractString, contractOffset, vulnerable) ->
    declarer = model.Position.NORTH
    contractOffset ?= 0
    vulnerable ?= false
    score = controller.ScoreCalculator.scoreFor(
        model.Contract.fromString(contractString),
        vulnerable,
        contractOffset)
    equal score, expectedScore


test "scoreFor basic", ->
    expectScore 80, '1H'
    expectScore 110, '1H', 1
    expectScore 140, '1H', 2
    expectScore 120, '1N', 1

    expectScore -50, '1H', -1
    expectScore -100, '1H', -2

    expectScore -3400, '1HXX', -7

    expectScore 260, '1HX', 1
    expectScore 360, '1HX', 2


test "scoreFor partscore vulnerability", ->
    expectScore -100, '1H', -1, true
    expectScore -100, '1H', -2, false
    expectScore -100, '1H', -1, true
    expectScore -50, '1H', -1, false


test "scoreFor games", ->
    expectScore 400, '3N'
    expectScore 420, '4H'
    expectScore 420, '4S'
    expectScore 400, '5C'
    expectScore 400, '5D'


test "scoreFor slams", ->
    expectScore 1440, '7C'
    expectScore 1440, '7D'
    expectScore 1510, '7H'
    expectScore 1510, '7S'
    expectScore 1520, '7N'

test "scoreFor from wikipedia", ->
    # http://en.wikipedia.org/wiki/Bridge_scoring#Duplicate_bridge
    expectScore 110, '2H', 0, true
    expectScore 110, '2H', 0, false
    expectScore 470, '2Hx', 0, false
    expectScore 660, '3N', +2, true
    expectScore 240, '1Dx', +1, false
    expectScore 1600, '5Sxx', +1, true
    expectScore 1020, '6N', +1, false
    expectScore -150, '4D', -3, false
    expectScore -500, '4Dx', -3, false
    expectScore -800, '4Dx', -3, true
