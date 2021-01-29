
class BidderFight
    constructor: ->
        @setupView()

    updateView: ->
        # FIXME: Maybe we'll make this smarter some day.
        @setupView()

    setupView: ->
        content = document.body
        $(content).empty()

        board = new model.Board
        controller.Autobidder.bidAllHands board, (board, callHistory) =>
            historyTable = view.CallHistoryTable.fromBoardAndHistory(board, callHistory)
            content.appendChild historyTable
        # Fight button.

$ ->
    window.mainController = new BidderFight
