import type { Metadata } from "next";
import "@fontsource/stix-two-text/400.css";
import "@fontsource/stix-two-text/500.css";
import "@fontsource/stix-two-text/600.css";
import "@fontsource/stix-two-text/700.css";
import "@fontsource/stix-two-text/400-italic.css";
import "./globals.css";

export const metadata: Metadata = {
  title: "Astrolabe",
  description: "A content-addressed knowledge graph for mathematics",
};

export default function RootLayout({
  children,
}: {
  children: React.ReactNode;
}) {
  return (
    <html lang="en" className="h-full overflow-hidden" suppressHydrationWarning>
      <head>
        <script
          dangerouslySetInnerHTML={{
            __html: "try{if(localStorage.getItem('theme')==='light')document.documentElement.classList.add('light')}catch(e){}",
          }}
        />
      </head>
      <body className="h-full overflow-hidden">{children}</body>
    </html>
  );
}
