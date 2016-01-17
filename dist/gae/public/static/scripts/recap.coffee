class BoardResultParser
    constructor: (@pairList) ->

    _pairFromText: (pairText, direction) ->
        # e.g. E10-Pyle-Bleemer
        [identifier, lastNameOne, lastNameTwo] = pairText.split('-')
        section = identifier[0]
        
        if section in '123456789'
            # If the first letter of the identifier is a digit, we must just have a single section.
            section = undefined
            pairNumber = parseInt(identifier)
        else
            pairNumber = parseInt(identifier.substr(1))

        pair = @pairList.pairBySectionAndDirectionAndNumber(section, direction, pairNumber)
        # Some recaps are missing pairs in the summary text, so we have to add them at result parse time. :(
        if not pair
            console.assert pair, "Unknown pair: " + pairText + " direction: " + direction
            pair = new Pair [new Player lastNameOne, new Player lastNameTwo]
            @pairList.addPair(pair, section, direction, pairNumber)
        return pair

    _parsePairsFromText: (pairsText) ->
        # e.g. E10-Pyle-Bleemer vs E4-Staver-Chase
        [nsPairText, ewPairText] = pairsText.split(' vs ')
        nsPair = @_pairFromText(nsPairText, 'NS')
        ewPair = @_pairFromText(ewPairText, 'EW')
        return [nsPair, ewPair]

    _strainCharFromText: (strainText) ->
        return {
            '\u2663': 'C',
            '\u2666': 'D',
            '\u2665': 'H',
            '\u2660': 'S',
            'NT': 'N'
        }[strainText]

    _parseContractAndDeclarer: (contractText) ->
        if contractText in ["Pass", "", "NP"]
             return [null, null]

        parts = contractText.split(' ')
        if parts.length == 4
            [levelText, strainText, doubleText, declarerText] = parts
        else
            [levelText, strainText, declarerText] = parts
            doubleText = ""
        
        contract = model.Contract.fromString(levelText + @_strainCharFromText(strainText) + doubleText)
        declarer = model.Position.fromChar(declarerText)
        return [contract, declarer]

    _computeContractOffsetFromScore: (contract, vulnerable, declarerScore) ->
        if not contract
            return 0  # Pass out case.
        if declarerScore < 0
            possibleOffsets = [-1..-13]
        else
            possibleOffsets = [0..6]
        for contractOffset in possibleOffsets
            if declarerScore == controller.ScoreCalculator.scoreFor(contract, vulnerable, contractOffset)
                return contractOffset
        console.assert false, "Failed to find possible contract offset for " + contract.name + " with score " + declarerScore
        return 0  # This is wrong, but we have nothing better to return.

    parseMatchResultsFromResultTable: (board, resultTable) ->
        matchResults = []
        for row, index in $('tr', resultTable)
            if index < 2
                # Skip the first two header rows.
                continue
            console.assert row.cells.length in [6, 7], "Results table has an unrecognized number of cells per row! (" + row.cells.length + ")"
            if row.cells.length == 7
                [contractCell, trickCountCell, nsScoreCell, ewScoreCell, nsMatchpointsCell, ewMatchpointsCell, pairsCell] = row.cells
            else
                [contractCell, nsScoreCell, ewScoreCell, nsMatchpointsCell, ewMatchpointsCell, pairsCell] = row.cells

            [contract, declarer] = @_parseContractAndDeclarer(contractCell.textContent)

            nsScore = parseInt(nsScoreCell.textContent)
            ewScore = parseInt(ewScoreCell.textContent)

            if trickCountCell
                declarerTrickCount = parseInt(trickCountCell.textContent)
                contractOffset = if contract then declarerTrickCount - 6 - contract.level else 0
            else
                if declarer
                    # If we are parsing an old replay w/o a trickCountCell, MatchBoardResult
                    # will have to divine the contractOffset from the score. :(
                    if declarer in [model.Position.NORTH, model.Position.SOUTH]
                        declarerScore = if nsScore then nsScore else -ewScore
                    else
                        declarerScore = if ewScore then ewScore else -nsScore

                    vulnerable = board.vulnerability.isVulnerable(declarer)
                    contractOffset = @_computeContractOffsetFromScore(contract, vulnerable, declarerScore)
                else
                    # Pass-out
                    declarerTrickCount = 0
                    contractOffset = 0


            nsMatchpoints = parseFloat(nsMatchpointsCell.textContent)
            ewMatchpoints = parseFloat(ewMatchpointsCell.textContent)

            [nsPair, ewPair] = @_parsePairsFromText(pairsCell.textContent)

            matchResult = new MatchBoardResult(board, nsPair, ewPair, declarer, contract, contractOffset, nsMatchpoints, ewMatchpoints)
            # Make sure our computed scores match the ones we read from the results table.
            console.assert not nsScore or matchResult.nsScore == nsScore, "" + matchResult.nsScore + " != " + nsScore + " for " + contractCell.textContent
            console.assert not ewScore or -matchResult.nsScore == ewScore, "" + -matchResult.nsScore + " != " + ewScore + " for " + contractCell.textContent

            matchResults.push matchResult
        return matchResults

    # FIXME: The parser may belong in its own separate class.
    parseBoardFromDiagram: (diagram) ->
        board = new model.Board

        for cell, index in $('td', diagram)
            # The first cell is all the board information.
            if index == 0
                # e.g. <b><i>Board 30</i></b><br>East Deals<br>None Vul
                summaryRegexp = /Board (\d+).+>(\w+) Deals.+(N-S|E-W|None|Both) Vul/
                matchResults = cell.innerHTML.match(summaryRegexp)
                board.number = +matchResults[1]
                board.dealer = model.Position.fromString(matchResults[2])
                board.vulnerability = model.Vulnerability.fromString(matchResults[3])

            pbnStringForHandCell = (cell) ->
                # West and East hands have a wrapping div.
                handHTML = if cell.firstChild.tagName == 'DIV' then cell.firstChild.innerHTML else cell.innerHTML

                handRegexp = /((?:\s\w\w?)*)<br>.*?((?:\s\w\w?)*)<br>.*?((?:\s\w\w?)*)<br>.*?((?:\s\w\w?)*)<br>/
                cardsInSuits = handHTML.match(handRegexp).slice(1).reverse() # Regexp returns cards in SHDC order.

                pbnString = (spaceSeparatedSuitStrings) ->
                    pbnStringsBySuit = spaceSeparatedSuitStrings.map (suitString) ->
                        cardRanks = $.trim(suitString).split(' ')
                        return cardRanks.map(model.Rank.pbnRankFromDisplayRank).join('')
                    return pbnStringsBySuit.join('.')
    
                return pbnString(cardsInSuits)

            # Cells 1, 2, 4, 6 hold the hands for the various positions.
            position = { 1: model.Position.NORTH, 2: model.Position.WEST, 9: model.Position.EAST, 11: model.Position.SOUTH }[index]
            if position?
                board.deal.hands[position.index()] = model.Hand.fromPBNString(pbnStringForHandCell(cell))

        # FIXME: This is fragile, but Board is not meant to be constructed and then modified!
        board.cachedDealIdentifier = board.deal.identifier()
        return board


class BridgeComposerParser
    constructor: (@document) ->


    @isBridgeComposerRecap: (document) ->
        return document.getElementsByClassName('bchd').length > 1

    resultsBlock: ->
        # Old bridge-composer recaps don't have id='bcrecap', otherwise we'd do: @document.getElementById('bcrecap')
        return @document.getElementsByTagName('pre')[0]

    parsePairsBySectionAndDirectionAndNumber: ->
        resultsBlock = @resultsBlock()
        pairsBySectionAndDirectionAndNumber = {}
        matchpointsByPair = {}
        percentileByPair = {}
        currentSection = null
        currentDirection = null
        for line in resultsBlock.textContent.split('\n')
            line = jQuery.trim(line)
            parts = line.split(' ')

            # It looks like it should be -3, but there are 2 spaces before and after the section!
            if parts[parts.length - 5] == "Section"
                currentSection = parts[parts.length - 3]
                pairsBySectionAndDirectionAndNumber[currentSection] ?= {}
                directionString = parts[parts.length - 1]
                currentDirection = {'East-West': 'EW', 'North-South': 'NS'}[directionString]
                pairsBySectionAndDirectionAndNumber[currentSection][currentDirection] ?= {}
                continue

            # This is a hack to identify lines with pair names in them.
            # the last fields in the form "Bob Jones - Jane Jones".
            if parts[parts.length - 3] != '-'
                continue

            firstPlayerName = parts.slice(-5, -3).join(' ')
            firstPlayer = new Player firstPlayerName
            secondPlayerName = parts.slice(-2).join(' ')
            secondPlayer = new Player secondPlayerName
            pairNumber = parseInt(parts[0])

            pair = new Pair [firstPlayer, secondPlayer]

            if not currentSection
                console.log "Ignoring pair: " + pair.displayString() + " no current section!"
                continue

            pairsBySectionAndDirectionAndNumber[currentSection][currentDirection][pairNumber] = pair

            # This regexp is from http://bytes.com/topic/javascript/answers/165013-how-javascript-trim-normalize-space-functions
            # I suspect we could use something simpler.
            line = line.replace(/^\s*|\s(?=\s)|\s*$/g, "") # Simplify whitespace to make lookups easier.
            parts = line.split(' ')
            stratificationPercentile = parseFloat(parts[1])
            matchpoints = parseFloat(parts[2])
            percentileByPair[pair.displayString()] = stratificationPercentile
            matchpointsByPair[pair.displayString()] = matchpoints
        return [pairsBySectionAndDirectionAndNumber, matchpointsByPair, percentileByPair]

    boardDiagramsAndResultTables: ->
        boardDiagrams = $('table.bchd', @document)
        resultTables = $('table.bcst', @document)

        if resultTables.length == 0
            boardDiagrams = []
            # In some recaps both the diagrams and the result tables have class='bchd'.
            $('table.bchd', @document).each (index, object) ->
                if index % 2
                    resultTables.push(object)
                else
                    boardDiagrams.push(object)

        return [boardDiagrams, resultTables]


class MatchBoardResult
    constructor: (@board, @nsPair, @ewPair, @declarer, @contract, @contractOffset, @nsMatchpoints, @ewMatchpoints) ->
        if @contract
            console.assert @declarer, "No declarer for " + @contract + " on board " + @board.number
            vulnerable = @board.vulnerability.isVulnerable(@declarer)
            @nsScore = controller.ScoreCalculator.northSouthScoreFor(@contract, vulnerable, @contractOffset, @declarer)
        else
            @nsScore = 0 # pass out


class BoardResult
    constructor: (@board, @matchResults, @diagram, @resultTable) ->
        # Board and MatchResults are the interesting members, @diagram and @resultTable
        # are just convenient places to store references into the bridge-composer recap document.
        # FIXME: We should consider @diagram and @resultTable elsewhere.

    @fromBridgeComposerDiagramAndResultTable: (pairList, diagram, resultTable) ->
        boardResultParser = new BoardResultParser pairList

        board = boardResultParser.parseBoardFromDiagram(diagram)
        matchResults = boardResultParser.parseMatchResultsFromResultTable(board, resultTable)

        return new BoardResult board, matchResults, diagram, resultTable


class Player
    constructor: (@name) ->
        


class Pair
    constructor: (@players) ->
        # Sorting the player names is kinda a hack.
        @players.sort (a, b) ->
            return a.name < b.name

    displayString: ->
        return (player.name for player in @players).join(' - ')


class PairList
    constructor: (@pairsBySectionAndDirectionAndNumber) ->


    sectionNames: ->
        return Object.keys(@pairsBySectionAndDirectionAndNumber)

    _objects: (dictionary) ->
        # There must be a nicer way to do this...
        return (dictionary[key] for key of dictionary)

    pairsInSection: (section) ->
        ewPairs = @_objects @pairsBySectionAndDirectionAndNumber[section]['EW']
        nsPairs = @_objects @pairsBySectionAndDirectionAndNumber[section]['NS']
        return ewPairs.concat nsPairs

    addPair: (pair, section, direction, number) ->
        sectionNames = @sectionNames()
        if sectionNames.length == 1
            section ?= sectionNames[0]
        @pairsBySectionAndDirectionAndNumber[section] ?= {}
        @pairsBySectionAndDirectionAndNumber[section][direction] ?= {}
        @pairsBySectionAndDirectionAndNumber[section][direction][number] = pair

    pairBySectionAndDirectionAndNumber: (section, direction, number) ->
        sectionNames = @sectionNames()
        if sectionNames.length == 1
            section ?= sectionNames[0]
        directionsBySection = @pairsBySectionAndDirectionAndNumber[section]
        if not directionsBySection
            return null
        pairsBySection = directionsBySection[direction]
        if not pairsBySection
            return null
        return pairsBySection[number]


class Recap
    constructor: (@pairList, @boardResults, @matchpointsByPair, @percentileByPair) ->

    boardResultsForBoard: (board) ->
        for boardResult in @boardResults
            if boardResult.board == board
                return boardResult

    @_sumMatchpointsByPair: (boardResults) ->
        matchpointsByPair = {}
        for boardResult in boardResults
            for matchResult in boardResult.matchResults
                matchpointsByPair[matchResult.ewPair.displayString()] ?= 0
                matchpointsByPair[matchResult.nsPair.displayString()] ?= 0
                matchpointsByPair[matchResult.ewPair.displayString()] += matchResult.ewMatchpoints
                matchpointsByPair[matchResult.nsPair.displayString()] += matchResult.nsMatchpoints
        return matchpointsByPair

    @_validateComputedMatchpoints: (computedMatchpointsByPair, expectedMatchpointsByPair) ->
        for pairName of computedMatchpointsByPair
            computedMatchpoints = computedMatchpointsByPair[pairName]
            computedMatchpoints = Math.round(computedMatchpoints * 100) / 100 # Round to 2 places.
            expectedMatchpoints = expectedMatchpointsByPair[pairName]

            diff = computedMatchpoints - expectedMatchpoints
            diff = Math.round(diff * 100) / 100 # Round to 2 places.
            assertMessage = "" + computedMatchpoints + " != " + expectedMatchpoints + " (" + diff + ") for " + pairName
            console.assert diff == 0, assertMessage

    @fromBridgeComposerDocument: (document) ->
        bridgeComposerParser = new BridgeComposerParser document
        # FIXME: These variables should be rolled into a single object.
        [pairsBySectionAndDirectionAndNumber, parsedMatchpointsByPair, percentileByPair] = bridgeComposerParser.parsePairsBySectionAndDirectionAndNumber()
        pairList = new PairList pairsBySectionAndDirectionAndNumber
        [boardDiagrams, resultTables] = bridgeComposerParser.boardDiagramsAndResultTables()

        boardResults = []
        for diagram, index in boardDiagrams
            # FIXME: We probably don't want to store these bridge-composer tables on BoardResult.
            boardResults.push BoardResult.fromBridgeComposerDiagramAndResultTable(pairList, diagram, resultTables[index])

        matchpointsByPair = Recap._sumMatchpointsByPair(boardResults)
        Recap._validateComputedMatchpoints(matchpointsByPair, parsedMatchpointsByPair)
        # FIXME: Once we have the matchpoint calculations working, we should validate the percentiles too.

        return new Recap pairList, boardResults, matchpointsByPair, percentileByPair


class RecapAnnotator
    constructor: (recap) ->
        @parser = new BridgeComposerParser document
        @recap = recap
        @playerColorPairs = [
            ['Seidel', 'lightgreen'],
            ['Barth', 'lightorange'],
            ['Bortz', 'yellow'],
            ['Huben', 'lightblue'],
            ['Price', 'lightpink'],
            # ['Guo', 'pink'],
            # ['Lin', 'red'],
        ]

    recordAutobidResult: (board, callHistory) ->
        resultTable = @recap.boardResultsForBoard(board).resultTable
        newRow = resultTable.insertRow(-1)
        # Make our row background match the alternating row colors.
        if resultTable.rows.length > 1
            newRow.style.backgroundColor = resultTable.rows[resultTable.rows.length - 3].style.backgroundColor
        contractCell = newRow.insertCell(-1)
        contractCell.appendChild view.ContractAndDeclarerView.fromHistory(callHistory)

        blankCellCount = (resultTable.rows[2].cells.length - 2)
        for count in [0...blankCellCount]
            newRow.insertCell(-1)

        pairNameCell = newRow.insertCell(-1)
        bidderLink = document.createElement 'A'
        round = model.Round.fromBoardAndCallHistory(board, callHistory)
        bidderLink.href = '/bid/' + round.identifier()
        bidderLink.textContent = "SAYCBridge Autobidder"
        pairNameCell.appendChild bidderLink

        historyTable = view.CallHistoryTable.fromBoardAndHistory(board, callHistory)
        resultTable.parentNode.insertBefore(historyTable, resultTable)

    highlightRowsWithKnownPlayers: (rows) ->
        for row in rows
            for [playerName, color] in @playerColorPairs
                if row.innerHTML.indexOf(playerName) != -1
                    row.style.backgroundColor = color


    highlightLinesWithKnownPlayers: (preTag) ->
        lines = preTag.textContent.split('\n')
        $(preTag).empty()
        for line in lines
            # Whitespace is ignored in divs, so we create a \n text node instead.
            if line == ""
                preTag.appendChild document.createTextNode('\n')
                continue

            lineNode = document.createElement 'div'
            lineNode.textContent = line
            preTag.appendChild lineNode
            for [playerName, color] in @playerColorPairs
                if line.indexOf(playerName) != -1
                    lineNode.style.backgroundColor = color

    createNavigationBar: (boardNumbers) ->
        navigationBar = document.createElement 'div'
        navigationBar.className = 'navigation'
        navigationBar.textContent = "Boards: "
        for boardNumber in boardNumbers
            boardLink = document.createElement 'a'
            boardLink.href = '#Board' + boardNumber
            boardLink.textContent = boardNumber
            navigationBar.appendChild boardLink
            navigationBar.appendChild document.createTextNode " "
        return navigationBar

    _createMatchpointsTable: (matchpointsByPair) ->
        matchpointsTable = document.createElement 'table'
        $(matchpointsTable).addClass('computedmatchpoints')
        $(matchpointsTable).addClass('tablesorter')
        headerRow = matchpointsTable.createTHead().insertRow(-1)
        headerRow.appendChild document.createElement('th')
        headerRow.lastChild.textContent = "Pair Name"
        headerRow.appendChild document.createElement('th')
        headerRow.lastChild.textContent = "Total Matchpoints"
        tbody = document.createElement('tbody')
        matchpointsTable.appendChild tbody
        for pairName of matchpointsByPair
            matchpoints = matchpointsByPair[pairName]
            row = tbody.insertRow(-1)
            row.insertCell(-1).textContent = pairName
            matchpoints = Math.round(matchpoints * 100) / 100 # Round to 2 places.
            row.insertCell(-1).textContent = matchpoints
        return matchpointsTable

    applyAnnotations: ->
        @highlightRowsWithKnownPlayers $('table.bcst tr')
        @highlightLinesWithKnownPlayers @parser.resultsBlock()

        boardNumbers = (boardResult.board.number for boardResult in @recap.boardResults)
        boardNumbers.sort (a,b) -> return a - b
        # FIXME: Should this grab the document off the Recap?
        document.body.appendChild @createNavigationBar(boardNumbers)

        for boardResult in @recap.boardResults
            controller.Autobidder.bidAllHands boardResult.board, (board, callHistory) =>
                @recordAutobidResult(board, callHistory)

        matchpointsTable = @_createMatchpointsTable(@recap.matchpointsByPair)
        $(matchpointsTable).tablesorter()
        document.body.appendChild matchpointsTable


class RecapSummaryController
    constructor: ->
        @percentileArraysByPair = {}
        @stdDeviationsArraysByPair = {}
        @sectionsArraysByPair = {}
        @recapNames = [
            # '06-06', # does not parse yet.
            # '06-13', # does not parse yet.
            # '06-20', # does not parse yet.
            # '06-27', # does not parse yet.
            # '07-04', # does not parse yet.
            '07-11',
            '07-18',
            # '07-25', # does not parse yet.
            # '08-01', # does not parse yet.
            # '08-08', # does not parse yet.
            '08-15',
            '08-22',
            '08-29', # Has no contract offset column
            '09-05', # Has no contract offset column
            '09-12',
            '09-19',
            '09-26', # Only has a single section 'A'
            # '10-03',  # Has combined sections E/F which confuses parsing.
            '10-10',
            '10-17',
            # No recap for 10-24?
            '10-31',  # The results are broken.
            '11-07',
            '11-14',
            '11-21',
        ]
        # This should be shared with RecapAnnotator.
        @playerColorPairs = [
            ['Seidel', 'lightgreen'],
            ['Barth', 'lightorange'],
            ['Bortz', 'yellow'],
            ['Huben', 'lightblue'],
            ['Price', 'lightpink'],
        ]

    _createDocumentFromHTML: (data) ->
        dummyDocument = document.implementation.createHTMLDocument()
        dummyDocument.open()
        dummyDocument.write(data)
        dummyDocument.close()
        return dummyDocument

    _average: (array) ->
        return array.reduce((a, b) -> a + b) / array.length

    _stdDev: (array) ->
        normalAvg = @_average(array)
        squares = (item * item for item in array)
        squaresAvg = @_average(squares)
        variance = Math.abs(squaresAvg - (normalAvg * normalAvg))
        return Math.sqrt(variance)

    _urlForRecap: (recapName) ->
        return '/recaps/' + recapName + '.html'

    _loadRecaps: ->
        for recapURL in (@_urlForRecap(name) for name in @recapNames)
            $.get recapURL, (data, textStatus, jqXHR) =>
                recap = Recap.fromBridgeComposerDocument @_createDocumentFromHTML(data)

                percentilesBySection = {}
                for section in recap.pairList.sectionNames()
                    percentilesBySection[section] = []
                    for pair in recap.pairList.pairsInSection(section)
                        pairName = pair.displayString()
                        percentile = recap.percentileByPair[pairName]
                        # Ignore pairs for which we don't have a percentile.
                        if percentile
                            percentilesBySection[section].push percentile
                        # Record that the pair played in this section.
                        @sectionsArraysByPair[pairName] ?= []
                        @sectionsArraysByPair[pairName].push section

                stdDevBySection = {}
                for section of percentilesBySection
                    percentiles = percentilesBySection[section]
                    stdDevBySection[section] = @_stdDev(percentiles)

                for section of stdDevBySection
                    stdDev = stdDevBySection[section]
                    for pair in recap.pairList.pairsInSection(section)
                        pairName = pair.displayString()
                        @stdDeviationsArraysByPair[pairName] ?= []
                        percentile = recap.percentileByPair[pairName]
                        stdDeviations = (percentile - 50) / stdDev
                        @stdDeviationsArraysByPair[pairName].push stdDeviations

                for pairName of recap.percentileByPair
                    @percentileArraysByPair[pairName] ?= []
                    @percentileArraysByPair[pairName].push recap.percentileByPair[pairName]

                @updateView()

    pageLoaded: ->
        @setupView()
        @_loadRecaps()

    _createHeaderCell: (text) ->
        headerCell = document.createElement('th')
        headerCell.textContent = text
        return headerCell

    _createRankingsTable: ->
        rankingsTable = document.createElement 'table'
        $(rankingsTable).addClass('computedmatchpoints')
        $(rankingsTable).addClass('tablesorter')
        headerRow = rankingsTable.createTHead().insertRow(-1)
        headerRow.appendChild @_createHeaderCell("Pair Name")
        headerRow.appendChild @_createHeaderCell("Avg %")
        headerRow.appendChild @_createHeaderCell("Avg StdDevs")
        headerRow.appendChild @_createHeaderCell("Events")
        headerRow.appendChild @_createHeaderCell("Sections")
        tbody = document.createElement('tbody')
        rankingsTable.appendChild tbody
        return rankingsTable

    _createRecapLinks: ->
        linksDiv = document.createElement 'div'
        for recapName in @recapNames
            recapLink = document.createElement 'a'
            recapLink.textContent = recapName
            recapLink.href = @_urlForRecap(recapName)
            linksDiv.appendChild recapLink
            linksDiv.appendChild document.createTextNode ' '
        return linksDiv

    setupView: ->
        content = document.body
        @recapLinks = @_createRecapLinks()
        content.appendChild @recapLinks
        @rankingsTable = @_createRankingsTable()
        content.appendChild @rankingsTable
        $(@rankingsTable).tablesorter()

    updateView: ->
        $(@rankingsTable.tBodies[0]).empty()
        for pairName of @percentileArraysByPair
            percentileArray = @percentileArraysByPair[pairName]
            if percentileArray.length < 2
                continue
            row = @rankingsTable.tBodies[0].insertRow(-1)
            row.insertCell(-1).textContent = pairName

            percentileAverage = @_average(percentileArray)
            percentileAverage = Math.round(percentileAverage * 100) / 100 # Round to 2 places.
            row.insertCell(-1).textContent = percentileAverage

            stdDevsArray = @stdDeviationsArraysByPair[pairName]
            stdDevsAvg = @_average(stdDevsArray)
            stdDevsAvg = Math.round(stdDevsAvg * 100) / 100 # Round to 2 places.
            row.insertCell(-1).textContent = stdDevsAvg

            row.insertCell(-1).textContent = percentileArray.length

            row.insertCell(-1).textContent = @sectionsArraysByPair[pairName]

            for [playerName, color] in @playerColorPairs
                if pairName.indexOf(playerName) != -1
                    for cell in row.cells
                        cell.style.backgroundColor = color

        $(@rankingsTable).trigger("update")


$ ->
    if BridgeComposerParser.isBridgeComposerRecap(window.document)
        recap = Recap.fromBridgeComposerDocument document
        annotator = new RecapAnnotator recap
        annotator.applyAnnotations()
    else
        # Otherwise we're loading this document into the summary page.
        # FIXME: The summary page should really have its own script file.
        window.mainController = new RecapSummaryController
        window.mainController.pageLoaded()
