package com.saycbridge.bridge;

import android.app.Activity;
import android.content.res.Configuration;
import android.content.Intent;
import android.content.SharedPreferences;
import android.os.Bundle;
import android.view.KeyEvent;
import android.view.Menu;
import android.view.MenuInflater;
import android.view.MenuItem;
import android.webkit.WebView;

public class BridgeActivity extends Activity {
    WebView mWebView;

    @Override
    public void onCreate(Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);
        setContentView(R.layout.main);

        mWebView = (WebView) findViewById(R.id.webview);
        mWebView.getSettings().setJavaScriptEnabled(true);

        SharedPreferences settings = getPreferences(MODE_PRIVATE);
        String lastURL = settings.getString("lastURL", "http://www.saycbridge.com/");
        mWebView.loadUrl(lastURL);
    }

    @Override
    public boolean onKeyDown(int keyCode, KeyEvent event) {
        if ((keyCode == KeyEvent.KEYCODE_BACK) && mWebView.canGoBack()) {
            mWebView.goBack();
            return true;
        }
        return super.onKeyDown(keyCode, event);
    }

    @Override
    public boolean onCreateOptionsMenu(Menu menu) {
        MenuInflater inflater = getMenuInflater();
        inflater.inflate(R.menu.options, menu);
        return true;
    }

    @Override
    public boolean onOptionsItemSelected(MenuItem item) {
        switch (item.getItemId()) {
            case R.id.next_hand:
                mWebView.loadUrl("http://www.saycbridge.com/");
                break;
            case R.id.share:
                Intent intent = new Intent(Intent.ACTION_SEND);
                intent.setType("text/plain");
                intent.putExtra(Intent.EXTRA_TEXT, mWebView.getUrl());
                startActivity(Intent.createChooser(intent, "Share with"));
        }
        return true;
    }

    @Override
    public void onConfigurationChanged(Configuration newConfig) {
        // We override orientation and keyboardhidden changes and do nothing.
        // The WebView will auto-rotate, and everything will be fine.
        super.onConfigurationChanged(newConfig);
    }

    @Override
    protected void onPause(){
        super.onPause();

        // I believe this is necessary to make the WebView load the last URL it had open.
        // It may be possible to make the WebView do this automatically?
        SharedPreferences settings = getPreferences(MODE_PRIVATE);
        SharedPreferences.Editor editor = settings.edit();
        editor.putString("lastURL", mWebView.getUrl());
        editor.commit();
    }
}
