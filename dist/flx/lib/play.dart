import 'package:flutter/material.dart' hide Card;
import 'package:flutter/material.dart' as material show Card;
import 'package:saycbridge/model.dart';

class PlayHome extends StatefulWidget {
  const PlayHome({super.key});

  @override
  PlayHomeState createState() => PlayHomeState();
}

class PlayHomeState extends State<PlayHome> {
  late Deal deal;

  @override
  void initState() {
    reDeal();
    super.initState();
  }

  void reDeal() {
    setState(() {
      deal = Deal.random();
    });
  }

  @override
  Widget build(BuildContext context) {
    return Scaffold(
      appBar: AppBar(
        title: const Text('Play'),
      ),
      body: Material(
        child: PlayTable(deal),
      ),
      floatingActionButton: FloatingActionButton(
        onPressed: reDeal,
        child: const Icon(Icons.refresh),
      ),
    );
  }
}

class SuitLine extends StatelessWidget {
  final Hand hand;
  final Suit suit;
  const SuitLine(this.hand, this.suit, {super.key});

  @override
  Widget build(BuildContext context) {
    List<Card> cards = hand.matchingSuit(suit).toList();
    // Flip the sort to put spades on top.
    cards.sort((a, b) => -a.rank.index.compareTo(b.rank.index));
    String cardsString = cards.map((card) => card.rank.name).join(" ");
    return Row(
      children: [
        Text(suit.codePoint),
        Text(cardsString),
      ],
    );
  }
}

class HandSummary extends StatelessWidget {
  final Position position;
  final Hand hand;
  const HandSummary(this.position, this.hand, {super.key});

  @override
  Widget build(BuildContext context) {
    List<Suit> displayOrder = [
      Suit.spades,
      Suit.hearts,
      Suit.diamonds,
      Suit.clubs
    ];
    return material.Card(
      margin: const EdgeInsets.all(10),
      child: Padding(
        padding: const EdgeInsets.all(8.0),
        child: SizedBox(
          width: 100, // HACK?
          child: Column(
            crossAxisAlignment: CrossAxisAlignment.start,
            children: [
              Text(position.name),
              for (Suit suit in displayOrder) SuitLine(hand, suit),
            ],
          ),
        ),
      ),
    );
  }
}

class DealSummary extends StatelessWidget {
  final Deal deal;
  const DealSummary(this.deal, {super.key});

  HandSummary _hand(Position position) =>
      HandSummary(position, deal.handFor(position));

  @override
  Widget build(BuildContext context) {
    return Row(
      mainAxisAlignment: MainAxisAlignment.center,
      children: [
        _hand(Position.west),
        Column(
          children: [_hand(Position.north), _hand(Position.south)],
        ),
        _hand(Position.east),
      ],
    );
  }
}

List<Card> sortForDisplay(List<Card> unsorted) {
  // Alternating colors for now:
  List<Suit> suitOrder = [Suit.spades, Suit.hearts, Suit.clubs, Suit.diamonds];
  // Should eventually handle missing suits, trump, etc.
  List<Card> sorted = List.from(unsorted); // Is this copy needed?
  sorted.sort((a, b) {
    if (a.suit != b.suit) {
      return suitOrder.indexOf(a.suit).compareTo(suitOrder.indexOf(b.suit));
    }
    return -a.rank.index.compareTo(b.rank.index);
  });
  return sorted;
}

typedef CardSelectCallback = void Function(Card which);

class CardSpread extends StatelessWidget {
  final Hand hand;
  final CardSelectCallback selectCard;
  final Card? selectedCard;

  const CardSpread(this.hand, this.selectCard, {this.selectedCard, super.key});

  Widget _card(Card card) {
    return GestureDetector(
      onTapDown: (_) => selectCard(card),
      child: Container(
        decoration: BoxDecoration(
          border: const Border(
            top: BorderSide(),
            left: BorderSide(),
          ),
          color: (card == selectedCard) ? Colors.red : null,
        ),
        padding: const EdgeInsets.all(5),
        child: Column(
          children: [Text(card.rank.displayRank), Text(card.suit.codePoint)],
        ),
      ),
    );
  }

  @override
  Widget build(BuildContext context) {
    List<Card> sorted = sortForDisplay(hand.cards);
    return Row(
      mainAxisSize: MainAxisSize.min,
      children: [for (Card card in sorted) _card(card)],
    );
  }
}

class PlayControls extends StatefulWidget {
  final Hand hand;
  final Position position;
  final String playerName;

  const PlayControls(this.hand, this.position, this.playerName, {super.key});

  @override
  PlayControlsState createState() => PlayControlsState();
}

class PlayControlsState extends State<PlayControls> {
  Card? selected;

  @override
  Widget build(BuildContext context) {
    return Column(
      children: [
        CardSpread(widget.hand, (Card card) {
          setState(() {
            selected = card;
          });
        }, selectedCard: selected),
        Container(
          decoration: BoxDecoration(border: Border.all()),
          child: Row(
            children: [Text(widget.position.name), Text(widget.playerName)],
          ),
        ),
      ],
    );
  }
}

class CurrentTrick extends StatelessWidget {
  const CurrentTrick({super.key});

  @override
  Widget build(BuildContext context) {
    return const SizedBox(width: 200, height: 200);
  }
}

class PlayTable extends StatelessWidget {
  final Deal deal;
  final Position player = Position.south;

  const PlayTable(this.deal, {super.key});

  PlayControls _hand(Position position) => PlayControls(
      deal.handFor(position), position, position == player ? "You" : "");

  @override
  Widget build(BuildContext context) {
    return Center(
      child: Column(children: [
        const Text("Contract: 1S"),
        Row(
          mainAxisAlignment: MainAxisAlignment.center,
          children: [
            _hand(Position.west),
            Column(
              children: [
                _hand(Position.north),
                const CurrentTrick(),
                _hand(Position.south),
              ],
            ),
            _hand(Position.east),
          ],
        ),
      ]),
    );
  }
}
