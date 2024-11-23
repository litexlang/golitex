export class L_Cache {
  private messages: string[] = [];
  private currentMessage: string[] = [];

  constructor() {}

  newMessage(newMessage: string[]) {
    this.messages.push(...newMessage);
    this.currentMessage = newMessage;
  }

  getAllMessages() {
    return this.messages;
  }

  getCurrentMessage() {
    return this.currentMessage;
  }
}
