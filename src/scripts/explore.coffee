
class Explore
    constructor: ->
        # The help text is static to make it most accessible to search engines.
        @aboutDiv = document.getElementById('about')

        [@basePath, @callHistory] = @basePathAndCallHistoryFromPath(window.location.pathname)
        @setupView()

    basePathAndCallHistoryFromPath: (path) ->
        pathWithoutLeadingSlash = path[1..]
        if '/' in pathWithoutLeadingSlash
            [basePath, callsString] = pathWithoutLeadingSlash.split('/')
            basePath = "/" + basePath
        else
            basePath = path
            callsString = ""

        try
            callHistory = model.CallHistory.fromIdentifier(callsString)
        catch error
            callHistory = new model.CallHistory

        return [basePath, callHistory]

    pathForCallsString: (callsString) ->
        return "/explore/" + callsString

    saveState: ->
        callsString = @callHistory.identifier()
        urlForCurrentState = @pathForCallsString callsString
        # If we already have a history entry for the current URL, no need to save.
        if window.location.pathname == urlForCurrentState
            return

        state = { 'callsString': callsString }
        window.History.pushState state, "", urlForCurrentState

    updateFromState: (state) ->
        urlParser = document.createElement 'a'
        urlParser.href = state.url

        [@basePath, @callHistory] = @basePathAndCallHistoryFromPath(urlParser.pathname)
        @setupView()

    recordCall: (call) ->
        @callHistory.calls.push(call)
        @saveState()

    updateView: ->
        # FIXME: Maybe we'll make this smarter some day.
        @setupView()

    setupView: ->
        content = document.getElementById('content')
        $(content).empty()

        # FIXME: We probably don't want to display N/S/E/W as part of the CallHistory.
        board = new model.Board(1) # This is a hack, we just want a non-vuln board to display.
        historyTable = view.CallHistoryTable.fromBoardAndHistory(board, @callHistory)
        content.appendChild historyTable

        possibleCallTable = view.CallExplorerTable.fromCallHistory(@callHistory, @recordCall)
        content.appendChild possibleCallTable
        $('.bid_button', possibleCallTable).bind 'click', (event) =>
            callButton = event.target
            while callButton and not callButton.call
                callButton = callButton.parentNode
            @recordCall callButton.call

$ ->
    window.mainController = new Explore

    History.Adapter.bind window, 'statechange', (event) ->
        window.mainController.updateFromState(History.getState())
