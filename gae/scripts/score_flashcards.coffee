
class ScoreFlashcards
    constructor: ->
        # The about text is static to make it most accessible to search engines.
        @aboutDiv = document.getElementById('about')
        [@basePath, @resultString] = @basePathAndResultStringFromPath(window.location.pathname)
        if not @resultString
            @_showNext()
        @setupView()

    basePathAndResultStringFromPath: (path) ->
        pathWithoutLeadingSlash = path[1..]
        if '/' in pathWithoutLeadingSlash
            [basePath, resultString] = pathWithoutLeadingSlash.split('/')
            basePath = "/" + basePath
            try
                @_contractAndVulnerabityAndOffsetFromResultString resultString
            catch error
                resultString = ""
        else
            basePath = path
            resultString = ""
        return [basePath, resultString]

    pathForResultString: (resultString) ->
        return "/scoring/" + resultString

    saveState: ->
        urlForCurrentState = @pathForResultString @resultString
        # If we already have a history entry for the current URL, no need to save.
        if window.location.pathname == urlForCurrentState
            return

        state = { 'resultString': @resultString }
        window.History.pushState state, "", urlForCurrentState

    updateFromState: (state) ->
        urlParser = document.createElement 'a'
        urlParser.href = state.url

        [@basePath, @resultString] = @basePathAndResultStringFromPath(urlParser.pathname)
        @setupView()

    _randomIntBelow: (max) ->
        return Math.floor(Math.random() * max)

    _pickRandom: (list) ->
        return list[@_randomIntBelow(list.length)]

    _nextContractString: ->
        level = @_pickRandom([1..7])
        # Clubs/Diamonds and Hearts/Spades are scored the same, so make NT just as likely.
        strain = @_pickRandom(['C', 'D', 'H', 'S', 'N', 'N'])
        # Re-doubled contracts are very uncommon.
        doubledString = @_pickRandom(['', '', '', '', '', '', 'x', 'x', 'x', 'xx'])
        vulnerableString = @_pickRandom(['', 'V'])
        # Avoid impossible offsets
        maxOffset = Math.min(7 - level, 3) # More than +3 is not worth practicing.
        # Ask about positive results more often, since they're more intersting.
        contractOffset = @_pickRandom([-4..maxOffset].concat [0..maxOffset])
        offsetString = if contractOffset < 0 then contractOffset else "+" + contractOffset
        return "" + level + strain + doubledString + offsetString + vulnerableString

    _showNext: ->
        @resultString = @_nextContractString()
        @saveState()

    _contractAndVulnerabityAndOffsetFromResultString: (resultString) ->
        vulnerable = 'V' in resultString or 'v' in resultString
        contractAndOffsetString = resultString.replace(/V|v/, '')
        if '-' in contractAndOffsetString
            [contractString, offsetString] = contractAndOffsetString.split('-')
            contractOffset = -parseInt(offsetString)
        else if '+' in resultString
            [contractString, offsetString] = contractAndOffsetString.split('+')
            contractOffset = parseInt(offsetString)
        else
            contractString = contractAndOffsetString
            contractOffset = 0
        return [model.Contract.fromString(contractString), vulnerable, contractOffset]

    showAnswer: ->
        [contract, vulnerable, contractOffset] = @_contractAndVulnerabityAndOffsetFromResultString(@resultString)
        expectedAnswer = controller.ScoreCalculator.scoreFor(contract, vulnerable, contractOffset)
        $(@answerContainer).empty()
        @answerContainer.appendChild view.ScoreDetail.fromResultTuple(contract, vulnerable, contractOffset)

    checkAnswer: (answer) ->
        [contract, vulnerable, contractOffset] = @_contractAndVulnerabityAndOffsetFromResultString(@resultString)
        expectedAnswer = controller.ScoreCalculator.scoreFor(contract, vulnerable, contractOffset)
        $(@answerContainer).empty()
        statusDiv = document.createElement 'div'
        @answerContainer.appendChild statusDiv

        if Math.abs(answer) == Math.abs(expectedAnswer)
            statusDiv.textContent = "Correct!"
            statusDiv.className = 'correct'
        else
            statusDiv.textContent = "" + answer + " is incorrect"
            statusDiv.className = 'incorrect'
        @answerContainer.appendChild view.ScoreDetail.fromResultTuple(contract, vulnerable, contractOffset)

    _createAnswerButton: (value) ->
        answerButton = document.createElement 'div'
        $(answerButton).addClass('choice')
        $(answerButton).addClass('button')
        answerButton.textContent = value
        $(answerButton).click (event) =>
            @checkAnswer(value)
            event.preventDefault()
        return answerButton

    _generateFakeAnswer: (correctAnswer) ->
        while true
            if correctAnswer < 0
                # Negative results are always multiples of 50, so make our fake answers realistic:
                answer = -Math.abs(Math.floor((Math.random() * 8) - 4) * 50 + correctAnswer)
            else
                answer = Math.abs(Math.floor((Math.random() * 80) - 40) * 10 + correctAnswer)
            # 0 is never a valid answer, no need to generate it.
            if answer != 0 and answer != correctAnswer
                return answer

    _generatePossibleAnswers: (correctAnswer, count) ->
        possibleAnswers = []
        correctIndex = @_randomIntBelow(count)
        for index in [0...count]
            if index == correctIndex and correctAnswer not in possibleAnswers
                possibleAnswers.push correctAnswer
                continue

            while true
                answer = @_generateFakeAnswer(correctAnswer)
                if answer not in possibleAnswers
                    break
            possibleAnswers.push answer
        return possibleAnswers

    _createAnswerContainer: (correctAnswer) ->
        answerContainer = document.createElement 'div'
        answerContainer.className = 'answerbox'

        possibleAnswers = @_generatePossibleAnswers(correctAnswer, 4)
        answersDiv = document.createElement 'div'
        answersDiv.className = 'answers'

        answerGrid = view.GridView.createEmpty(2, 2)
        answerGrid.rows[0].cells[0].appendChild @_createAnswerButton(possibleAnswers[0])
        answerGrid.rows[0].cells[1].appendChild @_createAnswerButton(possibleAnswers[1])
        answerGrid.rows[1].cells[0].appendChild @_createAnswerButton(possibleAnswers[2])
        answerGrid.rows[1].cells[1].appendChild @_createAnswerButton(possibleAnswers[3])

        answersDiv.appendChild answerGrid
        answerContainer.appendChild answersDiv

        showAnswerButton = @_createShowAnswerButton()
        answerContainer.appendChild showAnswerButton

        return answerContainer

    _createNextButton: ->
        nextButton = document.createElement 'div'
        $(nextButton).addClass('next')
        $(nextButton).addClass('button')
        nextButton.textContent = 'next'
        $(nextButton).click (event) =>
            if window._gaq
                window._gaq.push ['_trackEvent', 'Scoring', 'Flashcards', 'show next']
            @_showNext()
            event.preventDefault()
        return nextButton

    _createShowAnswerButton: ->
        revealButton = document.createElement 'div'
        $(revealButton).addClass('reveal')
        $(revealButton).addClass('button')
        revealButton.textContent = 'show answer'
        $(revealButton).click (event) =>
            if window._gaq
                window._gaq.push ['_trackEvent', 'Scoring', 'Flashcards', 'show answer']
            @showAnswer()
            event.preventDefault()
        return revealButton

    _createScorePrompt: ->
        scorePrompt = document.createElement 'h4'
        scorePrompt.className = 'prompt'
        scorePrompt.textContent = "What is the score?"
        return scorePrompt

    _createContractBox: (contract, vulnerable, contractOffset) ->
        contractBox = document.createElement 'div'
        contractBox.className = 'contractbox'
        contractBox.appendChild view.ContractView.fromContract(contract)
        offsetString = if contractOffset < 0 then  " \u2212 " + -contractOffset + " " else " \u002b " + contractOffset + " "
        contractBox.appendChild document.createTextNode offsetString

        if vulnerable
            vulnerabilitySpan = document.createElement 'span'
            vulnerabilitySpan.className = if vulnerable then 'vulnerable' else 'nonvulnerable'
            vulnerabilitySpan.textContent = if vulnerable then 'Vul' else 'Non Vul'
            contractBox.appendChild vulnerabilitySpan
        return contractBox

    setupView: ->
        content = document.body
        $(content).empty()

        @scorePrompt = @_createScorePrompt()
        content.appendChild @scorePrompt

        [contract, vulnerable, contractOffset] = @_contractAndVulnerabityAndOffsetFromResultString(@resultString)
        expectedAnswer = controller.ScoreCalculator.scoreFor(contract, vulnerable, contractOffset)

        @contractBox = @_createContractBox(contract, vulnerable, contractOffset)
        content.appendChild @contractBox

        @answerContainer = @_createAnswerContainer(expectedAnswer)
        content.appendChild @answerContainer

        @nextButton = @_createNextButton()
        content.appendChild @nextButton

        content.appendChild @aboutDiv

$ ->
    window.mainController = new ScoreFlashcards

    History.Adapter.bind window, 'statechange', (event) ->
        window.mainController.updateFromState(History.getState())