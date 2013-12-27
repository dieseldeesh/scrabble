#15-112 Term Project
#Adhish Ramkumar
#aramkuma
#Section D
#Mentor: Andre Sutanto

from AnimationWithRetainedGraphics import *
import urllib2
from Tkinter import N,NW,W,SW,S,SE,E,NE,CENTER
import tkSimpleDialog
import tkMessageBox
import winsound, sys
import random

###################################################
#Scrabble
###################################################
#creates the piece at the necessary spots
class Tile(TextRectangle):
    #sets up some of the basic attributes of the playe'r's piece
    def __init__(self,left,top,right,bottom,color,textColor,lineWidth):
        super(Tile,self).__init__(left,top,right,bottom)
        self.lineWidth=lineWidth#width of tile
        self.color=color #color of the tile
        self.color2=textColor #color of the text
        self.textFill=textColor #color of the text
        self.text=None
        self.anchor="center"
        self.font="Helvetica 16"#size of letter
        self.numFont="Helvetica 8"#size of letter score
    
    #draws the piece
    def draw(self,canvas):
        if(self.text!=None):#draw the tile if there is one...
            self.fill=self.color
            self.textFill=self.color2
            super(Tile,self).draw(canvas)

#Creates the board and specifies the locations of the pieces
class BoardGame(AnimationWithRetainedGraphics):
    #sets up some of the basic attributes of the board and player's piece
    def __init__(self):
        self.color=Color(239,224,185)#color of cell
        self.colorOver=Color(228,176,74)#empty cell
        self.textColor=Color(100,59,15)#color of text
        #alternating color scheme for the board
        self.boardColor1="#FFFFFF" #Blank Cell Color
        self.boardColor2="#C65734" #Triple Word Color
        self.boardColor3="#E98E71" #Triple Letter Color
        self.boardColor4="#C6B734" #Double Letter Color
        self.boardColor5="#66D19B" #Double Word Color
        self.boardColor6="#91A4CF" #Center Cell Color
        #Let's us know if a tile has been taken from the hand or not
        self.letterJustSelected=False
        self.letterJustMoved=False
        #used for the distribution chart
        self.distribution = [9,2,2,4,12,2,3,2,9,1,
                             1,4,2,6,8,2,1,6,4,6,4,
                             2,2,1,2,1,2]
        #Possible tiles in scrabble (basically alphabet + BLANK)
        self.letters=["A","B","C","D","E","F","G","H","I","J","K","L","M",
                      "N","O","P","Q","R","S","T","U","V","W","X","Y","Z",
                      "BLANK"]
        #Some basic initial conditions that are self explanatory
        self.isGameOver=False
        self.passCounter=0#counts how many passTurns have occurred
        self.splashScreen=True
        self.instructions1=False
        self.instructions2=False
        self.instructions3=False
        self.dictionaryMode=False
        
        #makes sure the cool animation for the intro screen only happens once
        self.firstTime=True
        #used to prevent user from playing game when there is a message box
        self.messageBox=False
        
        #necessary for making the program slow down and not
        #skip the rest of the instructions when ENTER is pressed
        self.slowScreenShift=0

        #This is how I find out what cells have been selected in dictionaryMode
        self.dictionaryX1,self.dictionaryX2=0,0
        self.dictionaryY1,self.dictionaryY2=0,0
        self.dictionarySet=[]
        #colors for the buttons so I can change only one
        #to green when that button is pressed
        self.buttonColors=["#EFE0B9","#EFE0B9","#EFE0B9","#EFE0B9","#EFE0B9"]
        
        #This 2d list could have been made using the
        #if statements that were used to create the
        #actual board pattern, but that would cause this
        #list to be remade in every iteration which would be a waste.
        self.bonus=[
            ["T",1,1,2,1,1,1,"T",1,1,1,2,1,1,"T"],
            [1,"D",1,1,1,3,1,1,1,3,1,1,1,"D",1],
            [1,1,"D",1,1,1,2,1,2,1,1,1,"D",1,1],
            [2,1,1,"D",1,1,1,2,1,1,1,"D",1,1,2],
            [1,1,1,1,"D",1,1,1,1,1,"D",1,1,1,1],
            [1,3,1,1,1,3,1,1,1,3,1,1,1,3,1],
            [1,1,2,1,1,1,2,1,2,1,1,1,2,1,1],
            ["T",1,1,2,1,1,1,"D",1,1,1,2,1,1,"T"],
            [1,1,2,1,1,1,2,1,2,1,1,1,2,1,1],
            [1,3,1,1,1,3,1,1,1,3,1,1,1,3,1],
            [1,1,1,1,"D",1,1,1,1,1,"D",1,1,1,1],
            [2,1,1,"D",1,1,1,2,1,1,1,"D",1,1,2],
            [1,1,"D",1,1,1,2,1,2,1,1,1,"D",1,1],
            [1,"D",1,1,1,3,1,1,1,3,1,1,1,"D",1],
            ["T",1,1,2,1,1,1,"T",1,1,1,2,1,1,"T"]
            ]
        #these variables help with creating the timer
        self.delayCounter=0
        self.timeMinutes=1
        self.timeSeconds=0

        #holds the bonuses for a played word
        #helps incorporate double word, triple letter...
        self.scoreBonus=[]
        self.usedBonuses=[]

        #makes the 100 letter pile
        self.makePile()

        #keeps track of the tiles placed but not exactly played yet
        self.placedTiles=[]

        #allows me to cover the tiles inbetween turns
        self.coverTiles=False

        #used to prevent the user from doing
        #anything during the intro animation
        self.loading=True

        #holds the values for each tile
        self.values=[1,3,3,2,1,4,2,4,1,8,5,1,3,
                     1,1,3,10,1,1,1,1,4,4,8,4,10,0]
        self.currentPlayer=0#keeps track of the current player
        self.selectedLetter=None#keeps track of the current letter being moved
        #keeps track of what cells have been filled by tiles
        #Note: this only keeps track of cells that are filled by tiles that
        #are not played yet
        self.cellsFilled=[]
        #keeps track of which spot the selected letter came from
        self.letterIndex=None
        self.trade=False#used for the tradeTiles feature
        #these 4 variables are used for the drag tile feature
        self.movingLeft,self.movingTop=None,None
        self.movingRight,self.movingBottom=None,None

        super(BoardGame,self).__init__()

    def makePile(self):
        """
        Makes the 100 letter pile for scrabble
        """
        self.tilePile=[]
        for index in xrange(len(self.distribution)):
            for tileNum in xrange(self.distribution[index]):
                self.tilePile.append(self.letters[index])

    def getPlayerNames(self):
        """
        Gets the names of the players.
        Gives each player 7 tiles.
        Initializes a unique score counter for each player.
        """
        self.players=[]
        self.playerTiles=[]
        self.scores=[]
        for num in xrange(self.numOfPlayers):
            self.scores.append(0)
            self.playerTiles.append([])
            self.getSevenTiles(num)
            self.players+=[tkSimpleDialog.askstring("Name of Player %d"
                                                    %(num+1),"Name:")]
            if(type(self.players[num])!=str or len(self.players[num])==0):
                self.players[num]="Player %d" %(num+1)

    def straightLine(self,line):
        """
        Finds out if the tiles placed are is a straight line
        (same row or col)
        """
        lineNum=self.cellsFilled[0][line]
        for index in xrange(len(self.cellsFilled)):
            if(self.cellsFilled[index][line] != lineNum):
                return False
        return True

    def isNextTo(self):
        """
        Finds out if at least one of the current tiles placed
        is immediately next to at least one "fixed" placed tile.
        """
        for cell in self.cellsFilled:
            rows=[cell[0]+1,cell[0]-1,cell[0]+0,cell[0]+0]
            cols=[cell[1]+0,cell[1]+0,cell[1]+1,cell[1]-1]
            for index in xrange(len(rows)):
                if(rows[index]>=0 and rows[index]<15 and
                   cols[index]>=0 and cols[index]<15 and
                   self.board[rows[index]][cols[index]].text!=None
                   and (rows[index],cols[index]) not in self.cellsFilled):
                    return True
        return False

    def play(self):
        """
        Checks if the tiles played follow the rules of scrabble.
        If they do, the tiles are fixed on the board and it's the next
        player's turn.
        Else, the tile are recalled.
        """
        if(self.selectedLetter!=None):
            self.playerTiles[slf.currentPlayer][
                self.letterIndex]=self.selectedLetter
            self.placedTiles.pop(len(self.placedTiles)-1)
        skipRest=False
        if(len(self.cellsFilled)==0):
            skipRest=True
            text="You need to place tiles!"
            self.messageBox=True
            tkMessageBox.showwarning(title="Error", message=text)
            self.recall()#need to put down some tiles
        elif(self.board[7][7].text==None):
            skipRest=True
            text="You need to use the center tile!"
            self.messageBox=True
            tkMessageBox.showwarning(title="Error", message=text)
            self.recall()#need to use the center space first
        elif(not self.isNextTo() and (7,7) not in self.cellsFilled):
            skipRest=True
            text="Your word needs to build off of a pre-existing word!"
            self.messageBox=True
            tkMessageBox.showwarning(title="Error", message=text)
            self.recall()#needs to be connected to already played words
        if(not skipRest):
            sameRow,sameCol=False,False
            if(self.straightLine(0)):
                sameRow=True
                #same row
            elif(self.straightLine(1)):
                sameCol=True
                #same col
            if(sameRow==False and sameCol==False):
                text="Your tiles need to be in a straight line!"
                self.messageBox=True
                tkMessageBox.showwarning(title="Error", message=text)
                self.recall()
            else:
                wordList=[]
                scoreBonusList=[]
                scoreBonusCoordinates=[]
                row=self.cellsFilled[0][0]
                col=self.cellsFilled[0][1]
                if(len(self.cellsFilled)>1):
                    drow=(abs(self.cellsFilled[1][0]-row) !=0)
                    dcol=(abs(self.cellsFilled[1][1]-col) != 0)
                    possibleWord=self.findPlausibleWord(row,col,drow,dcol)
                else:
                    drow=1
                    dcol=0
                    possibleWord=self.findPlausibleWord(row,col,drow,dcol)
                wordList.append(possibleWord)
                scoreBonusList.append(self.scoreBonus)
                scoreBonusCoordinates.append(self.scoreBonusCoordinates)
                if(len(wordList[0])>1 and self.isWordLegal(wordList[0])):
                    for coordinates in self.cellsFilled:
                        row=coordinates[0]
                        col=coordinates[1]
                        possibleWord=self.findPlausibleWord(row,col,dcol,drow)
                        if(len(possibleWord)>1):
                            wordList.append(possibleWord)
                            scoreBonusList.append(self.scoreBonus)
                            scoreBonusCoordinates.append(self.scoreBonusCoordinates)
                    passRest=False
                    for index in xrange(len(wordList)):
                        if(not self.isWordLegal(wordList[index])):
                            passRest=True
                            text="%s is not a legal word!"%(
                                wordList[index].capitalize())
                            self.messageBox=True
                            tkMessageBox.showwarning(title="Error",
                                                     message=text)
                            self.recall()
                    if(not passRest):
                        self.usedAllLetters()
                        for word in xrange(len(wordList)):
                            self.wordScore(wordList[word],scoreBonusList[word],scoreBonusCoordinates[word])
                            for index in xrange(len(self.usedBonuses)):
                                self.bonus[self.usedBonuses[index][0]][
                                    self.usedBonuses[index][1]]=1
                        self.selectedLetter=None
                        self.placedTiles=[]
                        self.cellsFilled=[]
                        self.getSevenTiles(self.currentPlayer)
                        self.coverTiles=True
                        self.messageBox=True
                        text="Player %d are you ready?"%(
                            ((self.currentPlayer+1)%len(self.playerTiles))+1)
                        tkMessageBox.showinfo(title="Turn Change", message=text)
                        self.currentPlayer=(
                            (self.currentPlayer+1)%len(self.playerTiles))
                        self.coverTiles=False
                        self.messageBox=False
                        self.passCounter=0
                        self.bonus[7][7]=1
                        self.timeMinutes=1
                        self.timeSeconds=0
                elif(len(wordList[0])==1):
                    scoreBonusList=[]
                    scoreBonusCoordinates=[]
                    wordList=[]
                    possibleWord=self.findPlausibleWord(row,col,dcol,drow)
                    wordList.append(possibleWord)
                    scoreBonusList.append(self.scoreBonus)
                    scoreBonusCoordinates.append(self.scoreBonusCoordinates)
                    if(len(wordList[0])>1 and self.isWordLegal(wordList[0])):
                        self.wordScore(wordList[0],scoreBonusList[0],scoreBonusCoordinates[0])
                        for index in xrange(len(self.usedBonuses)):
                                self.bonus[self.usedBonuses[index][0]][
                                    self.usedBonuses[index][1]]=1
                        self.selectedLetter=None
                        self.placedTiles=[]
                        self.cellsFilled=[]
                        self.getSevenTiles(self.currentPlayer)
                        self.coverTiles=True
                        self.messageBox=True
                        tkMessageBox.showinfo(title="Turn Change",
                                              message="Player %d are you ready?"
                                              %(((self.currentPlayer+1)%len(
                                                  self.playerTiles))+1))
                        self.currentPlayer=((self.currentPlayer+1)%len(
                            self.playerTiles))
                        self.coverTiles=False
                        self.messageBox=False
                        self.passCounter=0
                        self.bonus[7][7]=1
                        self.timeMinutes=1
                        self.timeSeconds=0
                    else:
                        self.messageBox=True
                        tkMessageBox.showwarning(
                            title="Error",message="%s is not a legal word!"
                                                 %(wordList[0].capitalize()))
                        self.recall()#send a message saying it is not legal
                else:
                    self.messageBox=True
                    tkMessageBox.showwarning(title="Error",
                                             message="%s is not a legal word!"
                                             %(wordList[0].capitalize()))
                    self.recall()#send a message saying it is not legal

    def findPlausibleWord(self,row,col,drow,dcol):
        """
        Finds out what were the letters placed
        from left to right or top to bottom.
        """
        while((row-drow)>=0 and (col-dcol)>=0 and
              self.board[row-drow][col-dcol].text!=None):
            row-=drow
            col-=dcol
        word=""
        self.scoreBonus=[]
        self.scoreBonusCoordinates=[]
        self.usedBonuses=[]
        while(row<15 and col<15 and self.board[row][col].text!=None):
            word+=self.board[row][col].text
            self.usedBonuses.append((row,col))
            self.scoreBonus.append(self.bonus[row][col])
            self.scoreBonusCoordinates.append((row,col))
            row+=drow
            col+=dcol
        return word

    def isWordLegal(self,word):
        """
        Checks if the word is in the dictionary
        """
        if(word.upper() in self.dictionary):
            return True
        return False

    def passTurn(self):
        """
        Passes the turn to the next player
        """
        self.passCounter+=1
        if(self.passCounter<(len(self.playerTiles)*2)):
            
            self.recall()
            self.coverTiles=True
            self.messageBox=True
            self.redrawAll()
            tkMessageBox.showinfo(title="Turn Change",
                                  message="Player %d are you ready?"
                                  %(((self.currentPlayer+1)%len(
                                      self.playerTiles))+1))
            self.currentPlayer=((self.currentPlayer+1)%len(self.playerTiles))
            self.coverTiles=False
            self.messageBox=False
            self.timeMinutes=1
            self.timeSeconds=0
            self.dictionaryX1,self.dictionaryX2=0,0
            self.dictionaryY1,self.dictionaryY2=0,0
            self.dictionarySet=[]
        else:
            self.gameOver()

    def recall(self):
        """
        Resets the conditions of the game to that of the start of the
        current player's turn.
        """
        for tileSpot in xrange(len(self.playerTiles[self.currentPlayer])):
            if(self.playerTiles[self.currentPlayer][tileSpot]==""
               and len(self.placedTiles)>0):
                self.playerTiles[self.currentPlayer][
                    tileSpot]=self.placedTiles.pop(0)
        for cell in xrange(len(self.cellsFilled)):
            self.board[self.cellsFilled[cell][0]][self.cellsFilled[
                cell][1]].text=None
        self.cellsFilled=[]
        self.selectedLetter=None
        self.coverTiles=False
        self.messageBox=False

    def shuffle(self):
        """
        Shuffles the tiles in the hand of the current player.
        """
        random.shuffle(self.playerTiles[self.currentPlayer])

    def tradeTiles(self):
        """
        Trades the selected tiles of the current player.
        """
        self.passCounter=0
        self.tilePile+=self.placedTiles
        self.placedTiles=[]
        while("" in self.playerTiles[self.currentPlayer]):
            index=self.playerTiles[self.currentPlayer].index("")
            self.playerTiles[self.currentPlayer].pop(index)
        self.getSevenTiles(self.currentPlayer)
        self.trade=not self.trade
        self.coverTiles=True
        self.messageBox=True
        tkMessageBox.showinfo(title="Turn Change",
                              message="Player %d are you ready?"
                              %(((self.currentPlayer+1)%len(
                                  self.playerTiles))+1))
        self.currentPlayer=((self.currentPlayer+1)%len(self.playerTiles))
        self.coverTiles=False
        self.messageBox=False
        self.selectedLetter=None
        self.passCounter=0

    def createTiles(self):
        #creates a 2d list (board)
        self.randTiles=[]
        for tile in xrange(1000):
            left=random.randrange(self.buffer*-1,self.width-self.side,1)
            top=random.randrange(self.buffer*-1,self.height-self.side,1)
            right=left+self.side
            bottom=top+self.side
            self.randTiles.append(
                self.addShape(Tile(
                    left,top,right,bottom,self.color,self.textColor,1)))
            self.randTiles[tile].text=self.letters[random.randrange(0,26)]

    #sets up the actual board
    def run(self,width=1100,height=950):
        self.extra=200#marks the excess space on the board
        self.width=width#canvas width
        self.height=height#canvas height
        #Scrabble plays on a 15x15 board
        self.rows=15
        self.cols=15
        #the side length of a spot on the board
        self.side=(width-self.extra*2)/self.rows#sidelength of a tile/cell
        self.buffer=self.extra*3/4.0#width of the distribution chart
        self.dictionaryList = []#will hold the dictionary
        self.getDictionary(open("words.txt"))
        self.tileDimensions=[]#will hold the demensions of a tile
        self.createTiles()#generates the tiles
        #background music (Turned off for submission)
        winsound.PlaySound('Next Episode.wav',
                           winsound.SND_ASYNC | winsound.SND_LOOP)
        super(AnimationWithRetainedGraphics, self).run(width,height)

    def getDictionary(self,source):
        """
        creates the dictionary
        """
        for word in source:
            self.dictionaryList.append(word.upper().strip())
        self.dictionary=set(self.dictionaryList)

    def defineBlankTile(self):
        """
        Sets up the interface for naming what a placed blank tile should be.
        """
        tile = False
        while (type(tile)!=str or len(tile)!=1
                or tile.upper() not in self.letters):
            self.coverTiles=True
            self.messageBox=True
            tkMessageBox.showinfo(title="Blank Tile",
                                    message="Enter a single letter:")
            tile=tkSimpleDialog.askstring("Blank Tile","What Letter?")
        self.coverTiles=False
        self.messageBox=False
        return tile.lower()

    def createBoard(self):
        """
        creates a 2d list (board)
        """
        self.board=[]
        for row in xrange(self.rows):
            boardRow=[]
            for col in xrange(self.cols):
                self.left=col*self.side+self.buffer
                self.top=row*self.side+self.buffer
                self.right=(col+1)*self.side+self.buffer
                self.bottom=(row+1)*self.side+self.buffer
                boardRow.append(self.addShape(
                    Tile(self.left,self.top,self.right,self.bottom,
                         self.color,self.textColor,1)))
                boardRow[col].text=self.selectedLetter
            self.board.append(boardRow)

    def getSevenTiles(self,index):
        """
        Gives each player seven tiles if possible
        """
        while("" in self.playerTiles[index]):
            self.playerTiles[index].pop(self.playerTiles[index].index(""))
        while(len(self.playerTiles[index])<7 and len(self.tilePile)>0):
            randIndex=random.randint(0,len(self.tilePile)-1)
            self.playerTiles[index].append(self.tilePile.pop(randIndex))
        if(self.tilePile==0):
            gameOver=False
            for hand in self.playerTiles:
                if(len(hand)==0):
                    gameOver=True
            if(gameOver):
                self.gameOver()
        while(len(self.playerTiles[index])<7):
            self.playerTiles[index].append("")

    def tileRemainingPenalty(self):
        """
        At the end of the game, those players with tiles left
        lose the sum of the values of those tiles from the score.
        This same value, is then added to the player who finished
        all his or her tiles.
        """
        bonusScoreReceiver=None
        bonus=0
        for index in xrange(len(self.players)):
            subtractScore=0
            for letter in xrange(len(self.playerTiles[index])):
                if(self.playerTiles[index][letter] in self.letters):
                    subtractScore+=self.values[self.letters.index(
                        self.playerTiles[index][letter])]
            if(subtractScore==0):
                bonusScoreReceiver=index
            self.scores[index]-=subtractScore
            bonus+=subtractScore
        if(bonusScoreReceiver!=None):
            self.scores[bonusScoreReceiver]+=bonus

    def gameOver(self):
        """
        sets gameOver conditions
        """
        self.tileRemainingPenalty()
        self.highestScore=None
        self.winner=[]
        for index in xrange(len(self.players)):
            if(self.highestScore==None or
               self.scores[index]>self.highestScore):
                self.highestScore=self.scores[index]
                self.winner.append(self.players[index])
            elif(self.scores[index]==self.highestScore):
                self.winner.append(self.players[index])
        self.isGameOver=True

    #finds out if a player (and which player) is in a given spot
    def getTileStatus(self,row,col):
        """
        tells if a cell has already been filled or not
        """
        return self.board[row][col].text

    #places a player's piece at a given spot
    def setTile(self,row,col,tile,tileUsed):
        """
        sets the cell to the specified letter
        """
        if(tileUsed):
            self.selectedLetter=None
        self.board[row][col].text=tile

    def usedAllLetters(self):
        """
        Checks if a player has used all his letters or not
        """
        bonus=50
        for index in xrange(len(self.playerTiles[self.currentPlayer])):
            if(self.playerTiles[self.currentPlayer][index]!=""):
                bonus=0
        self.scores[self.currentPlayer]+=bonus

    def wordScore(self,word,bonus,bonusCoordinates):
        """
        Returns the score the word given.
        Also takes into account bonus value tiles!
        (i.e. double word or triple letter)
        """
        wordList=list(word)
        score=0
        multiplier=1
        for letter in xrange(len(wordList)):
            if(type(bonus[letter]) == int):
                if(wordList[letter] in self.letters):
                    score+=bonus[letter]*self.values[self.letters.index(
                        wordList[letter].upper())]
                    bonus[letter]=1
            else:
                if(bonus[letter]=="T"):
                    multiplier*=3
                    self.bonus[bonusCoordinates[
                        letter][0]][bonusCoordinates[letter][1]]=1
                if(bonus[letter]=="D"):
                    multiplier*=2
                    self.bonus[bonusCoordinates[
                        letter][0]][bonusCoordinates[letter][1]]=1
                if(wordList[letter] in self.letters):
                    score+=self.values[
                        self.letters.index(wordList[letter].upper())]
        score*=multiplier
        self.scores[self.currentPlayer]+=score

    def cellPressed(self, row, col):
        """
        Identifies which cell has been pressed
        """
        tile = self.getTileStatus(row, col)
        tileUsed=False
        if (tile == None):
            tileUsed=True
            if(self.selectedLetter=="BLANK"):
                tile=self.defineBlankTile()
            else:
                tile=self.selectedLetter
        self.setTile(row, col, tile,tileUsed)

    def timerFired(self):
        """
        Keeps track of time using the timer
        """
        if(not self.messageBox and not self.splashScreen and not
           self.instructions1 and not self.instructions2 and not
           self.instructions3):
            self.delayCounter+=1
            if(self.delayCounter>0 and self.delayCounter%4==0):
                if(self.timeMinutes==1):
                    self.timeMinutes-=1
                    self.timeSeconds=59
                else:
                    self.timeMinutes==0
                    self.timeSeconds-=1
            if(self.timeMinutes==0 and self.timeSeconds==0):
                self.movingLeft,self.movingTop=None,None
                self.movingRight,self.movingBottom=None,None
                self.passTurn()
        super(AnimationWithRetainedGraphics, self).timerFired()

    def keyPressed(self,event):
        """
        Allows the user to interact witht the program by hitting certain keys
        """
        if(self.instructions1 and self.slowScreenShift==10 and event.keysym=="Return"):
            self.instructions2=True
            self.instructions1=False
            self.slowScreenShift=0
        if(self.instructions2 and self.slowScreenShift==10 and event.keysym=="Return"):
            self.instructions3=True
            self.instructions2=False
            self.slowScreenShift=0
        if(self.instructions3 and self.slowScreenShift==10 and event.keysym=="Return"):
            self.splashScreen=True
            self.instructions3=False
            self.slowScreenShift=0
        if(not self.splashScreen and not self.instructions1
           and not self.instructions2 and not self.instructions3):
            if("" not in self.playerTiles[self.currentPlayer] and
               self.trade==False and (event.keysym=="d" or event.keysym=="D")):
                self.messageBox=True
                if(self.dictionaryMode==True):
                    tkMessageBox.showwarning(title="Dictionary",
                    message="You are now exitting dictionaryMode")
                else:
                    tkMessageBox.showwarning(
                        title="Dictionary",
                        message="You are now in dictionaryMode")
                    text1="Drag a box entirely over the"
                    text1+=" word you want to define."
                    tkMessageBox.showwarning(
                        title="Dictionary",
                        message=text1)
                    text2="If you change your mind on defining a"
                    text2+=" word...tap \"d\" again."
                    tkMessageBox.showwarning(
                        title="Dictionary",
                        message=text2)
                self.messageBox=False
                self.dictionaryMode=not self.dictionaryMode
            elif(self.trade and event.keysym=="Return"):
                self.tradeTiles()#need to recall all first
            elif("" in self.playerTiles[self.currentPlayer] and
                 (event.keysym=="d" or event.keysym=="D")):
                self.messageBox=True
                textmess="You cannot go into dictionary mode at this time."
                tkMessageBox.showwarning(title="Error",
                                         message=textmess)
                self.messageBox=False


    #identifies which spot on the grid has been selected
    def mousePressed(self,event):
        """
        allows the use to interact with the program by clicking on parts
        of the canvas
        """
        if(self.splashScreen and not self.loading and not self.instructions1
           and not self.instructions2 and not self.instructions3):
            if(event.y>=self.height*3/4 and event.y<=self.height*3/4+100):
                buttonSelected=False
                for box in xrange(1,4):
                    if(event.x>self.width*3*box/13 and
                       event.x<(self.width*3*box/13+100)):
                        self.numOfPlayers=box+1
                        buttonSelected=True
                if(buttonSelected):
                    self.getPlayerNames()
                    self.splashScreen=False
                    self.createBoard()
            if(event.y>=self.height/16 and event.y<=(self.height/16+100)
               and event.x>=(self.width*9/13)
               and event.x<=(self.width*11/13+100)):
                self.splashScreen=False
                self.instructions1=True
        if(not self.splashScreen and not self.loading and not self.instructions1
           and not self.instructions2 and not self.instructions3):
            if(not self.messageBox and self.dictionaryMode):
                self.dictionaryX1=event.x
                self.dictionaryY1=event.y
            if(not self.messageBox and not self.dictionaryMode):
                if(event.y>=self.side*self.cols+self.buffer+15 and
                   event.y<=self.height-5):
                    button=int((event.x-5)/(self.width/5.0))
                    if(event.x<=5+self.width/5.0*button+self.width/6.0):
                        self.buttonColors[button]="#DACBAA"
                        if(button==0):
                            self.play()
                        elif(button==1):
                            self.passTurn()
                        elif(button==2):
                            self.recall()
                        elif(button==3):
                            if("" not in self.playerTiles[self.currentPlayer]):
                                self.shuffle()#need to recall all first
                            else:
                                self.messageBox=True
                                msg="Some tiles are missing from your hand"
                                tkMessageBox.showwarning(
                                    title="Error",message=msg)
                                self.messageBox=False
                        elif(button==4):
                            if("" not in self.playerTiles[self.currentPlayer]):
                                if(not self.trade):
                                    self.messageBox=True
                                    insertedText="Click on the tiles"
                                    addedText=" you don't want and hit enter."
                                    messageText=insertedText+addedText
                                    tkMessageBox.showinfo(title="Trade Tiles",
                                                          message=messageText)
                                    otherText="Click on this button"
                                    otherText+=" again if you "
                                    otherText+="change your mind on"
                                    otherText+=" trading tiles."
                                    tkMessageBox.showinfo(title="Trade Tiles",
                                                          message=otherText)
                                    self.messageBox=False
                                else:
                                    self.recall()
                                self.trade=not self.trade
                            else:
                                textPut="Some tiles are missing from your hand"
                                self.messageBox=True
                                tkMessageBox.showwarning(title="Error",
                                                         message=textPut)
                                self.messageBox=False
                if((event.x<=(self.buffer*1.5+len(
                    self.playerTiles[0])*self.side)
                    and event.x>=self.buffer*1.5) and
                   (event.y>=self.top and event.y<=self.bottom)):
                    if(self.trade):
                        self.selectedLetter=None
                    tempIndex=int((event.x-self.buffer*1.5)/self.side)
                    self.tempIndex=tempIndex
                    self.letterJustSelected=True
                    if(self.playerTiles[self.currentPlayer][tempIndex]!=""):
                        if(self.selectedLetter!=None):
                            self.playerTiles[self.currentPlayer][
                                self.playerTiles[self.currentPlayer].index(
                                    "")]=self.selectedLetter
                            self.placedTiles.pop(self.placedTiles.index(
                                self.selectedLetter))
                        self.letterIndex=tempIndex
                        self.selectedLetter=self.playerTiles[
                            self.currentPlayer][
                            self.letterIndex]
                        if(self.selectedLetter != ""):
                            self.placedTiles+=[self.selectedLetter]
                        if(self.trade):
                            if(len(self.tilePile)<len(self.placedTiles)):
                                self.messageBox=True
                                msg="You cannot trade more tiles "
                                msg+="than there are letters left."
                                tkMessageBox.showwarning(
                                    title="Error",message=msg)
                                self.messageBox=False
                                self.recall()
                if((event.x<=(self.buffer+self.cols*self.side) and event.x>=
                    self.buffer)and (event.y>self.buffer and event.y<=(
                        self.side*self.rows+self.buffer)) and not self.trade):
                    row=int((event.y-self.buffer)/self.side)
                    col=int((event.x-self.buffer)/self.side)
                    if((row>=0 and row<15) and (col>=0 and col<15)):
                        if((row,col) in self.cellsFilled):
                            if(self.selectedLetter!=None):
                                self.playerTiles[self.currentPlayer][
                                    self.playerTiles[
                                        self.currentPlayer].index(
                                            "")]=self.selectedLetter
                                self.placedTiles.pop(self.placedTiles.index(
                                    self.selectedLetter))
                            self.letterJustMoved=True
                            self.rowMoved=row
                            self.colMoved=col

    def mouseMoved(self, event):
        """
        Allows the user to drag tiles around the screen
        """
        if(self.selectedLetter!=None):
            if(self.letterJustSelected):
                self.playerTiles[self.currentPlayer][
                    self.letterIndex]=""
                self.letterJustSelected=False
        if(self.letterJustMoved):
            if(self.board[self.rowMoved][
                self.colMoved].text not in self.letters):
                self.selectedLetter="BLANK"
            else:
                self.selectedLetter=self.board[
                    self.rowMoved][self.colMoved].text
            self.cellsFilled.pop(
                self.cellsFilled.index((self.rowMoved,self.colMoved)))
            self.board[self.rowMoved][self.colMoved].text=None
            self.rowMoved=None
            self.colMoved=None
            self.letterJustMoved=False
        if(not self.messageBox and not self.dictionaryMode
           and not self.splashScreen and not self.instructions1
           and not self.instructions2 and not self.instructions3
           and not self.trade and self.selectedLetter!=None):
                self.movingLeft=event.x-self.side/2
                self.movingTop=event.y-self.side/2
                self.movingRight=event.x+self.side/2
                self.movingBottom=event.y+self.side/2

    def straightLineWord(self,line):
        """
        Checks if the cells selected in dictionary mode
        are in a straight line
        """
        lineNum=self.dictionarySet[0][line]
        for index in xrange(len(self.cellsFilled)):
            if(self.cellsFilled[index][line] != lineNum):
                return False
        return True

    def mouseReleased(self, event):
        """
        Allows the user to interact with the program
        by releasing a key or two
        """
        if(self.selectedLetter!=None and self.trade):
            self.selectedLetter=None
            if(self.letterJustSelected):
                self.playerTiles[self.currentPlayer][
                    self.letterIndex]=""
                self.letterJustSelected=False
        self.buttonColors=["#EFE0B9","#EFE0B9","#EFE0B9","#EFE0B9","#EFE0B9"]
        if(not self.splashScreen and not self.instructions1 and not
           self.instructions2 and not self.instructions3):
            if(not self.messageBox and self.dictionaryMode):
                self.dictionaryX2=event.x
                self.dictionaryY2=event.y
                if(self.dictionaryX2<self.dictionaryX1):
                    storeVal=self.dictionaryX2
                    self.dictionaryX2=self.dictionaryX1
                    self.dictionaryX1=storeVal
                if(self.dictionaryY2<self.dictionaryY1):
                    storeVal=self.dictionaryY2
                    self.dictionaryY2=self.dictionaryY1
                    self.dictionaryY1=storeVal
                noBlanks=True
                for row in xrange(self.rows):
                    for col in xrange(self.cols):
                        left=col*self.side+self.buffer
                        top=row*self.side+self.buffer
                        right=(col+1)*self.side+self.buffer
                        bottom=(row+1)*self.side+self.buffer
                        if(left>=self.dictionaryX1 and top>=self.dictionaryY1
                           and right<=self.dictionaryX2
                           and bottom<=self.dictionaryY2):
                            if(self.board[row][col].text!=None):
                                self.dictionarySet.append((row,col))
                            else:
                                noBlanks=False
                wordIsFalse=True
                if(noBlanks==False):
                    self.messageBox=True
                    msg="You cannot select blank tiles."
                    tkMessageBox.showwarning(title="Error",
                                             message=msg)
                    self.messageBox=False
                elif(len(self.dictionarySet)==0):
                    self.messageBox=True
                    tkMessageBox.showwarning(title="Error",
                                             message="No tiles selected!")
                    self.messageBox=False
                elif(not(self.straightLineWord(0) or self.straightLineWord(1))):
                    self.messageBox=True
                    msg="Please only select one word."
                    tkMessageBox.showwarning(title="Error",
                                             message=msg)
                    self.messageBox=False
                else:
                    word=""
                    for cell in self.dictionarySet:
                        word+=self.board[cell[0]][cell[1]].text
                    if(word.upper() in self.dictionary):
                        self.messageBox=True
                        definition = self.generateWordDefinition(word.lower())
                        tkMessageBox.showinfo(title="Definition",
                                              message=definition)
                        self.dictionaryMode=False
                        wordIsFalse=False
                        self.messageBox=False
                    else:
                        self.messageBox=True
                        msg="Please select one whole word."
                        tkMessageBox.showwarning(title="Error",
                                                 message=msg)
                        self.messageBox=True
                if(wordIsFalse):
                    self.messageBox=True
                    msg="Try Again or hit \"d\" to exit."
                    tkMessageBox.showinfo(title="Definition Mode",
                                             message=msg)
                    self.messageBox=False
                self.dictionaryX1,self.dictionaryX2=0,0
                self.dictionaryY1,self.dictionaryY2=0,0
                self.dictionarySet=[]
            if(not self.messageBox and not self.dictionaryMode):
                if((event.x<=(self.buffer+self.cols*self.side) and event.x>=
                    self.buffer)and (event.y>self.buffer and event.y<=(
                        self.side*self.rows+self.buffer)) and not self.trade):
                    row=int((event.y-self.buffer)/self.side)
                    col=int((event.x-self.buffer)/self.side)
                    if((row>=0 and row<15) and (
                        col>=0 and col<15) and self.board[
                        row][col].text==None and self.selectedLetter!=None):
                        self.cellsFilled+=[(row,col)]
                        self.cellPressed(row,col)
                elif((event.x<=(self.buffer*1.5+len(
                    self.playerTiles[0])*self.side)
                    and event.x>=self.buffer*1.5) and
                   (event.y>=self.top and event.y<=self.bottom)
                     and self.selectedLetter!=None):
                    if(self.trade):
                        self.selectedLetter=None
                    else:
                        tempIndex=int((event.x-self.buffer*1.5)/self.side)
                        if(self.playerTiles[self.currentPlayer][
                            tempIndex]==""):
                            self.letterIndex=tempIndex
                            self.playerTiles[self.currentPlayer][
                                self.letterIndex]=self.selectedLetter
                            self.placedTiles.pop(self.placedTiles.index(
                                self.selectedLetter))
                            self.selectedLetter=None
                        elif(self.tempIndex==tempIndex):
                            self.placedTiles.pop(self.placedTiles.index(
                                self.selectedLetter))
                            self.selectedLetter=None
                        else:
                            self.letterIndex=self.playerTiles[
                                self.currentPlayer].index("")
                            self.playerTiles[self.currentPlayer][
                                self.letterIndex]=self.selectedLetter
                            self.placedTiles.pop(self.placedTiles.index(
                                self.selectedLetter))
                            self.selectedLetter=None
                else:
                    if(self.selectedLetter!=None and not self.trade):
                        self.letterIndex=self.playerTiles[
                            self.currentPlayer].index("")
                        self.playerTiles[self.currentPlayer][
                            self.letterIndex]=self.selectedLetter
                        self.placedTiles.pop(self.placedTiles.index(
                            self.selectedLetter))
                        self.selectedLetter=None
                self.movingLeft,self.movingTop=None,None
                self.movingRight,self.movingBottom=None,None

    #identifies the location of the square
    def getCellBounds(self,row,col):
        """
        Gets the coordinates of the tile
        """
        left=col*self.side
        right=(col+1)*self.side
        top=(row)*self.side
        bottom=(row+1)*self.side
        return (left,top,right,bottom)

    def createButtonOptions(self):
        """
        Creates the buttons at the bottom of the screen
        """
        buttons=["PLAY","PASS","RECALL","SHUFFLE","TRADE"]
        for button in xrange(5):
            left=5+self.width/5.0*button
            top=self.side*self.cols+self.buffer+15
            right=5+self.width/5.0*button+self.width/6.0
            bottom=self.height-5
            self.canvas.create_rectangle(left,top,right,bottom,
                                         fill=self.buttonColors[
                                             button], width=2)

            self.canvas.create_text((left+right)/2, (top+bottom)/2,
                                    text=buttons[button],
                                    fill="#B7521E",font="Papyrus %d bold"
                                    %(self.side/3.0),width=0)

    def displayPlayerTiles(self):
        """
        Shows the player's current hand
        """
        self.clearTileList()
        self.playerHand=[]
        for index in xrange(len(self.playerTiles[self.currentPlayer])):
            self.left=int(index*self.side+self.buffer*1.5)
            self.top=int((self.buffer-self.side)/2)
            self.right=int(self.left+self.side)-1#minus 1 for the border
            self.bottom=int(self.top+self.side)
            self.tileDimensions+=[(self.left,self.top,self.right,self.bottom)]
            if(self.playerTiles[self.currentPlayer][index]==""):
                self.playerHand.append(self.addTile(Tile(
                    self.left,self.top,self.right,
                    self.bottom,self.colorOver,self.colorOver,0)))
            else:
                self.playerHand.append(self.addTile(Tile(
                    self.left,self.top,self.right,
                    self.bottom,self.color,self.textColor,1)))
            if(self.playerTiles[self.currentPlayer][index]=="BLANK"):
                self.playerHand[index].text=" "
            else:
                self.playerHand[index].text=self.playerTiles[
                    self.currentPlayer][index]
    
    #creates the board graphic
    def redrawAll(self):
        """
        Clears all the graphics.
        Redraws all the graphics.
        (allows us to keep track of all the changes)
        """
        titleColor="#B7521E"
        textColor="#643B0F"
        boxColor="#EFE0B9"
        self.canvas.delete(ALL)
        if(self.isGameOver):
            self.canvas.create_rectangle(
                0,0,self.width+self.buffer,self.height,fill=boxColor, width=0)
            #run facebook login
            self.canvas.create_text(self.width/2, self.height/4,
                                    text="Game Over!", fill=titleColor,
                                    font="Papyrus 90 bold")
            if(len(self.winner)==1):
                winner=" & "
                winner+=self.winner[0]
            elif(len(self.winner)>1):
                winner=""
                for player in xrange(len(self.winner)):
                    winner+=" & "
                    winner+=self.winner[player]
            self.canvas.create_text(self.width/2, self.height/4*3,
                                    text="%s Won!" %(winner[3:]),
                                    fill=textColor, font="Papyrus 40 bold")
        elif(self.splashScreen):
            numOfPlayers=[2,3,4]
            self.canvas.create_text(self.width/2, self.height*1/4,
                                    text= "SCRABBLE", fill=titleColor,
                                    font="Papyrus 40 bold")
            self.canvas.create_text(self.width/2, self.height*27/40,
                                    text= "How Many Players?", fill=textColor,
                                    font="Papyrus 30 bold")
            for box in xrange(1,4):
                self.canvas.create_rectangle(self.width*3/13*box,
                                             self.height*3/4,
                                             self.width*3/13*box+100,
                                             self.height*3/4+100,
                                             fill=boxColor,width=1)
                self.canvas.create_text((self.width*6/13*box+100)/2,
                                        (self.height*6/4+100)/2,
                                        text=str(box+1),fill=textColor,
                                        font="Papyrus 20 bold")
            self.canvas.create_rectangle(self.width*9/13,
                                         self.height*1/16,
                                         self.width*11/13+100,
                                         self.height*1/16+100,
                                         fill=boxColor,width=1)
            self.canvas.create_text((self.width*20/13+100)/2,
                                    (self.height*1/8+100)/2,
                                    text="Instructions",
                                    fill=textColor,
                                    font="Papyrus 20 bold")
            if(self.firstTime==True):
                super(BoardGame,self).redrawAll()
                x=60
                while(x>0 and len(self.shapes)>0):
                    x-=1
                    self.shapes.pop(0)
                if(len(self.shapes)==0):
                    self.loading=False
                    self.firstTime=False
        elif(self.instructions1):
            self.gif1 = PhotoImage(file = 'Instructions1.gif')
            self.canvas.create_image(self.width/2, self.height/2, image = self.gif1)
            self.canvas.create_text(self.width-2.5*self.buffer,self.height-.5*self.buffer,
                                    text="Press enter to go to next page",
                                    fill="black",font="Helvetica 20 bold")
            while(self.slowScreenShift<10):
                self.slowScreenShift+=1
        elif(self.instructions2):
            self.gif2 = PhotoImage(file = 'Instructions2.gif')
            self.canvas.create_image(self.width/2, self.height/2, image = self.gif2)
            self.canvas.create_text(self.width-2.5*self.buffer,self.height-.5*self.buffer,
                                    text="Press enter to go to next page",
                                    fill="black",font="Helvetica 20 bold")
            while(self.slowScreenShift<10):
                self.slowScreenShift+=1
        elif(self.instructions3):
            self.gif3 = PhotoImage(file = 'Instructions3.gif')
            self.canvas.create_image(self.width/2, self.height/2, image = self.gif3)
            self.canvas.create_text(self.width-2.5*self.buffer,self.height-0.5*self.buffer,
                                    text="Press enter to go to back to homeScreen",
                                    fill="black",font="Helvetica 20 bold")
            while(self.slowScreenShift<10):
                self.slowScreenShift+=1
        else:
            downShift=(self.side*self.cols/2.0+self.buffer)/14.0
            self.canvas.create_text(2*self.buffer+5,
                                    self.buffer/5.0,text="Player Hand",
                                    fill=textColor, font="Helvetica 16 bold")
            if(self.timeSeconds>9):
                text="%d:%d"%(self.timeMinutes,self.timeSeconds)
            else:
                text="%d:0%d"%(self.timeMinutes,self.timeSeconds)
            self.canvas.create_rectangle(
                self.width-2*self.buffer-10,20,self.width+5-self.buffer,
                self.bottom+20,fill=boxColor,width=1)                    
            self.canvas.create_text((2*self.width+5-3*self.buffer)/2,
                (self.top)/2+15,text="Timer",fill=textColor,
                                    font="Helvetica %d bold" %(self.side/3))
            self.canvas.create_rectangle(
                self.width-2*self.buffer,self.top+15,
                self.width-5-self.buffer,
                self.bottom+15,fill="#333333",width=0)
            self.canvas.create_text((2*self.width+5-3*self.buffer)/2,(
                self.top+self.bottom)/2+15,text=text,fill="red",
                                    font="Helvetica %d bold" %(self.side/3))

            self.canvas.create_rectangle(5,self.side*self.cols/2.0-downShift,
                                         self.buffer-5,self.side*self.cols
                                         +self.buffer,fill=boxColor,width=2)

            self.canvas.create_text(75,self.side*self.cols/2.0-downShift/2,
                                    text="Distribution",fill=titleColor,
                                    font="Papyrus %d bold"%(self.side/3.5),
                                    width=0)

            for index in xrange(len(self.letters)/2):
                self.canvas.create_text(15,self.side*self.cols/2.0+downShift*
                                        index+15,text="%s - %d\t%s - %d "
                                        %(self.letters[index],
                                          self.distribution[index],
                                          self.letters[index+13],
                                          self.distribution[index+13]),
                                        fill=textColor,
                                        anchor="w",
                                        font="Papyrus %d bold"%(self.side/5.0),
                                        width=0)
            self.canvas.create_text(75,self.side*self.cols/2.0+downShift*13+15,
                                        text="Blank - 2",
                                        fill=textColor,
                                        font="Papyrus %d bold"%(self.side/5.0),
                                        width=0)
            
            self.canvas.create_rectangle(5,self.side*(self.cols/2-1.5),
                                         self.buffer-5,self.side+self.side*
                                         (self.cols/2-1.5),
                                         fill=boxColor,width=2)
            self.canvas.create_text(15,self.side*(self.cols/2-1),
                                    text="%d Tiles Left" %len(self.tilePile),
                                    fill=titleColor,
                                    font="Papyrus %d bold"%(self.side/4.0),
                                    anchor="w",
                                    width=0)

            self.canvas.create_rectangle(self.width-self.buffer*1.7,self.side*
                                         self.cols/2.0-downShift,
                                         self.width-self.buffer/4.0,
                                         self.side*self.cols-self.buffer,
                                         fill=boxColor,width=2)

            self.canvas.create_text(self.width-self.buffer+5,
                                    self.side*self.cols/
                                    2.0-downShift/2,
                                    text="Players",fill=titleColor,
                                    font="Papyrus %d bold"%(self.side/3.0),
                                    width=0)
           
            for index in xrange(len(self.players)):
                if(index==self.currentPlayer):
                    fillColor="red"
                else:
                    fillColor=textColor
                self.canvas.create_text(self.width-self.buffer*1.6,
                                        self.side*self.cols/2.0
                                        +downShift*index+15,
                                        text="%s - %d"
                                        %(self.players[index],self.scores[
                                            index]),fill=fillColor,anchor="w",
                                        font="Papyrus %d bold"%(self.side/3.0),
                                        width=0)

            self.canvas.create_rectangle(self.width-self.buffer*1.7,self.buffer,
                                         self.width-self.buffer/4.0,self.buffer*2
                                         ,fill=boxColor,width=2)

            self.canvas.create_text(self.width-self.buffer+5,self.buffer,
                                    text="Selected Letter:",fill=titleColor,
                                    font="Papyrus %d bold"%(self.side/3.0),
                                    anchor="n", width=0)
            if(self.selectedLetter!=None):
                letter=str(self.selectedLetter)
                val=str(self.values[self.letters.index(
                    self.selectedLetter)])
                if(val=="1"):
                    val+=" point"
                else:
                    val+=" points"
                
            else:
                letter=""
                val=""
            self.canvas.create_text(self.width-self.buffer+5,
                                    self.buffer+self.side,
                                    text=letter,fill=textColor,
                                    font="Papyrus %d bold"%(self.side/2),
                                    anchor="n",
                                    width=0)
            self.canvas.create_text(self.width-self.buffer+5,
                                    self.buffer+self.side*1.7,
                                    text=val,fill=textColor,
                                    font="Papyrus %d bold"%(self.side/2),
                                    anchor="n",
                                    width=0)

            for row in xrange(self.rows):
                for col in xrange(self.cols):
                    if(row==7 and col==7):
                        self.fill=self.boardColor6
                        text="S"
                    elif((((row==3 or row==11) and (col==0 or col==14))
                         or ((row==0 or row==14) and (col==3 or col==11))
                         or ((row==6 or row==8 or row==2 or row==12) and
                             (col==6 or col==8 or col==2 or col==12))
                         or ((col==7 and (row==3 or row==11))
                             or (row==7 and (col==3 or col==11))))
                         and not((row==2 or row==12) and (col==2 or col==12))):
                        self.fill=self.boardColor4
                        text="DL"
                    elif((row==0 or row==7 or row==14) and
                         (col==0 or col==7 or col==14)):
                        self.fill=self.boardColor2
                        text="TW"
                    elif((row==col or row+col==14) and not(row==5 or row==9)):
                        self.fill=self.boardColor5
                        text="DW"
                    elif((row-1)%4==0 and (col-1)%4==0):
                        self.fill=self.boardColor3
                        text="TL"
                    else:
                        self.fill=self.boardColor1
                        text=None
                    bounds=list(self.getCellBounds(row,col))
                    for index in xrange(len(bounds)):
                        bounds[index]+=self.buffer
                    self.canvas.create_rectangle(*bounds,
                                                 fill=self.fill,width=1)
                    
                    if(text!=None):
                        if(text=="S"):
                            self.canvas.create_oval(*bounds,
                                                    fill="#333333",width=1)
                        self.canvas.create_text((bounds[0]+bounds[2])/2,
                                                (bounds[1]+bounds[3])/2,
                                                text=text,fill="white",
                                                font="Helvetica %d bold"%(
                                                    self.side/3.5),
                                                width=0)
            self.createButtonOptions()
            self.displayPlayerTiles()
            super(BoardGame,self).redrawAll()
            if(self.movingLeft!=None):
                self.canvas.create_rectangle(self.movingLeft,self.movingTop,
                                             self.movingRight,self.movingBottom,
                                             fill=boxColor,width=1)
                if(self.selectedLetter=="BLANK"):
                    score=""
                    tileText=""
                else:
                    tileText=self.selectedLetter
                    score=self.values[self.letters.index(tileText)]
                self.canvas.create_text(
                    (self.movingRight+self.movingLeft)/2,
                    (((self.movingTop+self.movingBottom)/2
                      +self.movingTop)/2+(
                          self.movingTop+self.movingBottom)/2)/2,
                    text=tileText,fill=textColor,font="Helvetica 16")
                self.canvas.create_text(
                    (((self.movingLeft+self.movingRight)/2+self.movingRight)/2+(
                        self.movingLeft+self.movingRight)/2)/2,
                    ((self.movingTop+self.movingBottom)/2+self.movingBottom)/2,
                    text=score,fill=textColor, font="Helvetica 8")
            if(self.coverTiles):
                self.canvas.create_rectangle(220,50,550,100,
                                             fill="#E4B04A",width=0)
    #THE REST IS ESSENTIALLY NOT MY CODE...I editted it a bit...
    # Reads the content of a web page at a specified URL
    # Returns a list containing the lines of the fetched web page
    def grabWebPage(self,url):
      urlHandler = urllib2.urlopen(url)
      lines = urlHandler.readlines()
      urlHandler.close()
      return lines

    # Returns the substring contained between a left and a right delimiter
    def substringBetween(self,string, leftDelimiter, rightDelimiter):
      index1 = string.find(leftDelimiter) + len(leftDelimiter)
      index2 = string.find(rightDelimiter)
      return string[index1:index2]

    # Extracts information from a single line of text
    # Parameters:
    #   htmlLines is a list of lines
    #   lineIdentifier is a string contained only in the
    #   line that has the information we seek
    #   leftDelimiter, rightDelimiter are strings that
    #   surround the information we want to extract
    # Returns a string
    def wrapInfoInDocument(self,htmlLines, lineIdentifier,
                           leftDelimiter, rightDelimiter):
      for line in htmlLines:
        if lineIdentifier in line:
          info = self.substringBetween(line, leftDelimiter, rightDelimiter)
          return info

    # Wraps the price of gold from http://www.ticker.com
    # Returns a string
    def getDefinition(self,word):
      webLines = self.grabWebPage(
          'http://dictionary.reference.com/browse/%s?s=t'%(word))
      definition = self.wrapInfoInDocument(webLines, '<meta name="description"',
                                           'definition, ', ' See more."/>')
      return definition

    # Generates an HTML document including the current time in Pittsburgh,
    # and the current price of gold.
    # Returns a string
    def generateWordDefinition(self,word):
      definition = self.getDefinition(word)
      content = 'The definition of '+word+' is: '+ definition
      return content

###################################################
# ignore_rest
###################################################
def main():
    app = BoardGame()
    app.run()

main()
