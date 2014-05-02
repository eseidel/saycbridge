
class Explore
    constructor: ->
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

    _createClearButton: ->
        clearButton = document.createElement 'div'
        $(clearButton).addClass('clear')
        $(clearButton).addClass('button')
        clearButton.textContent = 'Clear'
        $(clearButton).click (event) =>
            @callHistory.calls = []
            @saveState()
            event.preventDefault()
        return clearButton

    setupView: ->
        content = document.getElementById('content')
        $(content).empty()

        # FIXME: We probably don't want to display N/S/E/W as part of the CallHistory.
        board = new model.Board(1) # This is a hack, we just want a non-vuln board to display.
        historyTable = view.CallHistoryTable.fromBoardAndHistory(board, @callHistory)
        content.appendChild historyTable

        content.appendChild @_createClearButton()

        callMenu = view.CallMenu.fromCallHistory(@callHistory, @recordCall)
        content.appendChild callMenu
        $('.call_description', callMenu).bind 'click', (event) =>
            callDescription = event.target
            while callDescription and not callDescription.call
                callDescription = callDescription.parentNode
            @recordCall callDescription.call

        content.appendChild @_createClearButton()


$ ->
    window.mainController = new Explore

    History.Adapter.bind window, 'statechange', (event) ->
        window.mainController.updateFromState(History.getState())
