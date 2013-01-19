//
//  BridgeViewController.m
//  Bridge
//
//  Created by Eric Seidel on 11/5/11.
//

#import "TargetConditionals.h"
#import "BridgeViewController.h"

#import "NSData+Base64.h"


@implementation BridgeViewController

- (UIWebView*) webView {
    return (UIWebView *)self.view;
}

- (void)didReceiveMemoryWarning
{
    // Releases the view if it doesn't have a superview.
    [super didReceiveMemoryWarning];
    
    // Release any cached data, images, etc that aren't in use.
}

#pragma mark - WebView Delegate

- (BOOL)webView:(UIWebView *)webView shouldStartLoadWithRequest:(NSURLRequest *)request navigationType:(UIWebViewNavigationType)navigationType
{
    // It appears that non-navigation loads come through this callback.  Those are all allowed.
    if (navigationType == UIWebViewNavigationTypeOther)
        return YES;

    // FIXME: Perhaps localhost should be simulator only?
    NSSet *allowedHosts = [NSSet setWithObjects:@"www.saycbridge.com", @"saycbot.appspot.com", @"saycbridge.com", "localhost", nil];
    NSURL *url = [request URL];
    NSArray *pathComponents = [url pathComponents];

    if ([allowedHosts containsObject:[url host]] && ([pathComponents count] < 2 || [pathComponents objectAtIndex:1] == @"bid"))
        return YES;

    [[UIApplication sharedApplication] openURL:url];
    return NO;
}

- (NSString *)iconAsDataURL
{
    NSString *iconPath = [[NSBundle mainBundle] pathForResource:@"apple-touch-icon-114x114" ofType:@"png"];
    NSData *iconAsData = [NSData dataWithContentsOfFile:iconPath];
    NSString *iconAsBase64 = [iconAsData base64EncodedString];
    return [@"data:image/png;base64," stringByAppendingString:iconAsBase64];
}

- (void)webView:(UIWebView *)webView didFailLoadWithError:(NSError *)error
{
    NSString *offlineHTMLPath = [[NSBundle mainBundle] pathForResource:@"offline" ofType:@"html"];
    NSError *decodingError = nil;
    NSString *offlineHTML = [NSString stringWithContentsOfFile:offlineHTMLPath encoding:NSUTF8StringEncoding error:&decodingError];
    offlineHTML = [offlineHTML stringByReplacingOccurrencesOfString:@"ICON_CONTENTS" withString:[self iconAsDataURL]];

    [webView loadHTMLString:offlineHTML baseURL:[NSURL URLWithString:@"http://www.saycbridge.com"]];
}

#pragma mark - View lifecycle

// Implement viewDidLoad to do additional setup after loading the view, typically from a nib.
- (void)viewDidLoad
{
    [super viewDidLoad];

#if TARGET_IPHONE_SIMULATOR
    NSURL *defaultURL = [NSURL URLWithString:@"http://localhost:8080/"];
#else
    NSURL *defaultURL = [NSURL URLWithString:@"http://www.saycbridge.com/"];
#endif

    NSString *offlineHTMLPath = [[NSBundle mainBundle] pathForResource:@"loading" ofType:@"html"];
    NSError *decodingError = nil;
    NSString *offlineHTML = [NSString stringWithContentsOfFile:offlineHTMLPath encoding:NSUTF8StringEncoding error:&decodingError];
    offlineHTML = [offlineHTML stringByReplacingOccurrencesOfString:@"ICON_CONTENTS" withString:[self iconAsDataURL]];
    // FIXME: This should load the last hand visited instead of the default url.
    offlineHTML = [offlineHTML stringByReplacingOccurrencesOfString:@"SERVER_URL" withString:[defaultURL absoluteString]];

    [self.webView loadHTMLString:offlineHTML baseURL:defaultURL];
}

- (void)viewDidUnload
{
    [super viewDidUnload];
    // Release any retained subviews of the main view.
    // e.g. self.myOutlet = nil;
}

- (BOOL)shouldAutorotateToInterfaceOrientation:(UIInterfaceOrientation)interfaceOrientation
{
    // Return YES for supported orientations
    return (interfaceOrientation == UIInterfaceOrientationPortrait);
}

@end
