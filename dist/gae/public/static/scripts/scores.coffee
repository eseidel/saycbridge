
class BridgeScores
    constructor: ->
        # The about text is static to make it most accessible to search engines.
        @aboutDiv = document.getElementById('about')

    _recordScore: (scoreToContractTuples, score, level, strainClass, doubledString, contractOffset, vulnerableString) ->
        strainClass ?= ""
        contractTuples = scoreToContractTuples[score]
        contractTuples ?= []
        contractTuples.push [level, strainClass, doubledString, contractOffset, vulnerableString]
        scoreToContractTuples[score] = contractTuples

    _contractsByScore: ->
        scoreToContractTuples = {}
        for level in [1..7]
            for strain in "CHN" # C/D are scored the same, as are H/S.
                bidString = "" + level + strain
                for doubledString in ["", "x", "xx"]
                    contract = model.Contract.fromString(bidString + doubledString)
                    for vulnerableString in ["", "V"]
                        for overtrickCount in [0..(7-level)]
                            # Vulnerability only matters for doubled overtricks or game bonus.
                            if vulnerableString == "V"
                                if not contract.isGameOrAbove() and (overtrickCount == 0 or doubledString == "")
                                    continue
                            score = controller.ScoreCalculator.scoreFor(contract, vulnerableString == "V", overtrickCount)
                            @_recordScore(scoreToContractTuples, score, level, strain, doubledString, overtrickCount, vulnerableString)

        for doubledString in ["", "x", "xx"]
            for vulnerableString in ["", "V"]
                for undertrickCount in [1..13]
                    # Only vulnerability and doubledness matters for undertricks, so just always calculate from 7N.
                    contract = model.Contract.fromString("7N" + doubledString)
                    score = controller.ScoreCalculator.penaltyForUndertricks(contract, vulnerableString == "V", undertrickCount)
                    @_recordScore(scoreToContractTuples, score, null, null, doubledString, -undertrickCount, vulnerableString)
        return scoreToContractTuples

    _cmpTuples: (a, b) ->
        [levelA, strainCharA, doubledStringA, contractOffsetA, vulnerableStringA] = a
        [levelB, strainCharB, doubledStringB, contractOffsetB, vulnerableStringB] = a
        levelDiff = levelB - levelA
        if levelDiff
            return levelDiff

        strainDiff = strainCharB - strainCharA
        if strainDiff
            return strainDiff

        doubleDiff = doubledStringB - doubledStringA
        if doubleDiff
            return doubleDiff

        offsetDiff = contractOffsetB - contractOffsetA
        if contractOffsetB < 0 and contractOffsetA < 0
            offsetDiff *= -1  # This doesn't seem to affect the sort order yet?
        if offsetDiff
            return offsetDiff

        return vulnerableStringB - vulnerableStringA

    setupView: ->
        content = document.body
        content.appendChild @aboutDiv

        scoresTable = document.createElement 'table'
        headerRow = scoresTable.insertRow(-1)
        headerRow.className = 'header'
        headerRow.insertCell(-1).textContent = "Non Vul"
        headerRow.insertCell(-1).textContent = "Score"
        headerRow.insertCell(-1).textContent = "Vul"

        scoreToContractTuples = @_contractsByScore()

        allScores = []
        for score of scoreToContractTuples
            allScores.push score

        allScores.sort (a, b) =>
            return a - b

        for score in allScores
            scoreRow = scoresTable.insertRow(-1)
            nonVulCell = scoreRow.insertCell(-1)
            nonVulCell.className = 'nonvulnerable'
            scoreCell = scoreRow.insertCell(-1)
            scoreCell.textContent = score
            scoreCell.className = 'score'
            vulCell = scoreRow.insertCell(-1)
            vulCell.className = 'vulnerable'

            contractTuples = scoreToContractTuples[score]
            contractTuples.sort @_cmpTuples

            for contractTuple in contractTuples
                [level, strainChar, doubledString, contractOffset, vulnerableString] = contractTuple

                contractSpan = document.createElement 'span'
                contractSpan.className = "contract"
                if not level
                    contractSpan.appendChild document.createTextNode "O"
                else
                    contractSpan.appendChild document.createTextNode level
                    strain = model.Strain.fromChar(strainChar)
                    contractSpan.appendChild view.StrainView.fromStrain(strain)

                contractSpan.appendChild document.createTextNode doubledString

                contractOffsetString = ""
                if contractOffset > 0
                    contractOffsetString += "+"
                if contractOffset != 0
                    contractOffsetString += contractOffset
                contractSpan.appendChild document.createTextNode contractOffsetString
                contractSpan.appendChild document.createTextNode vulnerableString
                if vulnerableString == "V"
                    targetCell = vulCell
                else
                    targetCell = nonVulCell
                
                targetCell.appendChild contractSpan
                targetCell.appendChild document.createTextNode " "

        content.appendChild scoresTable

$ ->
    scores = new BridgeScores
    scores.setupView()
