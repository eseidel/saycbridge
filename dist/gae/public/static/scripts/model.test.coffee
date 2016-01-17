module "CallHistory"


possibleNextCalls = (historyString) ->
    callHistory = CallHistory.fromCallsStringAndDealerChar(historyString, 'N')
    return callHistory.possibleNextCalls()


test "possibleNextCalls", ->
    calls = possibleNextCalls('')
